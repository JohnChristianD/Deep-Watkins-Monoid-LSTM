# Deep Watkins RNN

Agda-first Q8.24 recurrent, distributional reinforcement-learning prototype.
The canonical learner is `FullCoupled/CanonicalLearnerMonolith.agda`.
This README is the repository's only project documentation.

The canonical Agda import surface is intentionally preserved:

```agda
open import Haskell.Prelude public
open import Haskell.Data.Int public
open import Haskell.Data.Bits public
open import Agda.Builtin.Equality.Rewrite public
```

The learner uses Int32 Q8.24 values, widened Int64 intermediates, saturating
narrowing, and explicit fixed-point approximations. Agda2HS extracts the
Haskell-compatible declarations; GHC checks the extracted module in CI.

The learner has no explicit strict-field annotations. When strict fields are
needed, Agda2HS provides `Haskell.Prim.Strict`: its `Strict` record maps to
Haskell's `unboxed-strict` representation. The builtin
`Agda.Builtin.Strict` forcing primitives are not part of this learner's
import surface.

## Learner

The recurrent feature cell has one scalar hidden feature. Its bounded input
feature uses shifted/rescaled Quantmoid4:

```text
feature_t = 2 * Quantmoid4(x_t / 2) / 126 - 1
gate_t    = hard_sigmoid(feature_t + w_g * hidden_(t-1))
candidate = ReLU(feature_t + w_c * hidden_(t-1))
hidden_t  = ReLU((1 - gate_t) * hidden_(t-1) + gate_t * candidate)
```

The Quantmoid4 integer forward map and smooth-shadow CHAD derivative are
separate functions. The shadow derivative is a training surrogate for the
smooth tanh-like approximation, not the derivative of integer rounding.
Standard IQN cosine features remain cosine; they are not replaced by
Quantmoid4.

Two independently parameterized, live dueling IQN32 critics (A and B) replace
the actor-critic. Each critic has a noisy value head and non-empty per-action
noisy advantage heads. Each quantile uses a 32-component cosine embedding.
Dueling advantage centering is performed across actions at each quantile.

The host supplies all quantile fractions and factorized NoisyNet noise. The
pure Agda learner performs no hidden random draws. The 32 current quantiles
and 32 target quantiles form a 32-by-32 quantile-Huber objective.

## Online action/value update

The update is Double distributional SARSA(0):

1. The active live critic selects one next action.
2. The other live critic evaluates that exact action; it does not select a
   second action.
3. The active critic receives the sole critic update for this transition.
4. The selected action and its required recurrent/noise state are carried
   into the following transition.

The active critic alternates A/B after every environment transition. At
each transition, the active critic selects the next action and the other live
critic evaluates that exact action. Exactly one critic is updated; the
selected action and the peer's noise sample are carried into the next call.
After the alternation, that peer becomes the active critic and consumes the
carried action/noise pair for its current-state update. Each call performs
exactly one critic update (UTD = 1 under the caller's one-call-per-transition
contract). There is no replay buffer or replay path, no delayed target copy,
no actor, and no multi-step return. The caller must advance the state and
pending decision exactly once; ordinary Agda function types do not statically
enforce affine use. Terminal targets contain reward only; nonterminal targets
bootstrap once from the peer critic's quantiles for the selected action.

At `lambda = 0`, the Dutch eligibility trace does not become zero or vanish:
it collapses to the current feature, `e_t = x_t`. The historical accumulation
term is absent, and the true-online correction cancels algebraically. The
resulting parameter update is the ordinary one-step SARSA(0) semi-gradient
update. Quantile regression makes the target distributional; it does not
restore a nontrivial eligibility history. The recurrent CHAD reverse scan is
a gradient calculation through the current recurrent computation, not a
multi-step return.

## Optimizer

Every learned parameter carries IDBD state: weight, log step size, sensitivity,
and a diagonal curvature estimate. The log step size is projected in Euclidean
distance onto the declared Q8.24 interval `[-8, 0]`. A separate
`l2GradientDecay` coefficient adds the L2 term to the data gradient before
the parameter update. The learner has no global gradient clipping,
max-gradient normalization, or implicit fixed weight shrink.

The diagonal curvature field makes this a diagonal IDBD approximation, not a
full-Hessian optimizer. The exponential used for the step size is an explicit
bounded Q8.24 approximation.

## Recurrent differentiation and resource ownership

`iterativeCHAD` stores recurrent primal frames and scans them newest-to-oldest,
threading the future hidden cotangent and accumulating recurrent parameter
cotangents. Its local VJP uses the Quantmoid4 smooth-shadow derivative and the
piecewise derivatives of the hard-sigmoid and ReLU operations.

`PendingDecision` packages the selected action, recurrent cache, current
quantile fractions, and peer-noise sample. The transition function threads
that package into the following update. This packages the intended
single-consumption boundary, but ordinary Agda function types are unrestricted:
the current network API does not yet prove affine use by a linear context
checker. Trebor Huang's `agda-linear` is a useful reference for encoding
resource occurrences and disjoint context splitting; Bend is a separate
affine language, not an Agda dependency.

## Build and verification

Typed Teal sources under `.ci/teal` drive the CI, parallel Agda checks,
RUSS inventory, and static Pages generation. Teal type-checks these programs
and compiles them to Lua; the generated programs run on LuaJIT. LuaFun is pinned
by Nix, and Lua Lanes runs isolated Agda workers. The LuaFun source audit bans
only the contraction/repetition family `duplicate`, `replicate`, `xrepeat`,
and `cycle`. Operations such as `split`, `span`, `partition`, `tabulate`,
`zeros`, `ones`, and random generators are outside that ban.

CI checks Teal types, Agda, Agda2HS extraction, GHC typechecking, the LuaFun
source audit, the RUSS inventory, and the static Pages artifact. The small
Bool definitions in Agda are executable sanity checks, not a substitute for
a comprehensive test suite.


## Build performance diagnosis

The GitHub Actions run [#45549279892](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45549279892) provides a concrete failure trace. The Nix development-shell command began at 04:49:09 UTC on 25 November 2026 and failed at 05:03:15 UTC, after about 14 minutes. Both the Nix-store cache and the Agda/interface cache missed. Nix then attempted to build the `Agda-2.9.0` Haskell derivation from source. Its log reached modules 408 through 431 of 491 before the `Setup build` process was killed; Nix reported exit status 137. That status indicates SIGKILL. Runner memory pressure is the leading explanation, although the log contains no kernel OOM record proving the killer's reason.

The failure happened while Nix was building the Agda compiler itself. The downstream `agda2hs-1.5` derivations failed because their Agda dependency failed. That run never reached the learner's Agda checks, Agda2HS extraction, or the separate `ghc-check -fno-code` invocation. The available evidence therefore identifies a cold Nix/Haskell toolchain build as the measured bottleneck; it does not establish that typechecking the generated learner module is slow.

The earlier workflow used the combined Nix cache action, whose save phase runs after the job. The failed job skipped that phase, so successful store paths from the attempt were not persisted. The workflow now restores and saves the Nix store in separate steps, with the save step running even after a failed build. The Agda interface cache also uses `save-always`. A committed `flake.lock` keeps the dependency graph and Nix cache key stable. Saving the store preserves completed dependencies, although Nix cannot resume the failed Agda derivation's deleted temporary build directory.

The CI driver now reports wall time for each checked stage and each isolated Agda worker. The generated-Haskell check also emits GHC phase timings and RTS allocation/residency statistics. The Nix shell runs with build logs enabled and reports its overall wall time. These measurements will separate the cost of building the toolchain, checking the Agda modules, extracting Haskell, and checking the extracted learner.

A MAlonzo reset is not part of this repair. The canonical CI path invokes the `agda2hs-agda` wrapper with `--disable-backend`, then runs Agda2HS extraction; it does not invoke Agda's `--compile`/MAlonzo backend. Deleting `MAlonzo/` therefore cannot fix the observed Nix derivation failure. Deleting cached `.agdai` interfaces would instead force more Agda work.

A reinstall or blind Agda2HS/Agda upgrade is also not indicated. The current flake pins Agda2HS to `2f89c9adc5018aa34bf4ed715750d30c088fdcb7` and its Agda 2.9.0 source dependency. The current build failure is a source-build resource/cache problem, not evidence of a broken installation or an incompatible Agda2HS release. Keep those pins until the new timings show a problem in the generated-module check or a tested upstream release offers a concrete fix.

Still required before treating the learner as validated:

- numeric reference tests for Q8.24 arithmetic, Quantmoid4 pieces, cosine
  approximation, IDBD projection, and NoisyNet zero-noise parity;
- tests for current/target quantile sample separation, 32-by-32 loss
  weighting, action alignment, alternating critic ownership, and terminal
  targets;
- finite-difference or high-precision reference checks for the recurrent
  smooth-shadow VJP and the complete critic gradient;
- a type-level affine transition proof and end-to-end environment training
  evaluation.

The implementation is a prototype until those checks pass.
