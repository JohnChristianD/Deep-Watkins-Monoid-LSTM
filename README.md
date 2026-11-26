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
and compiles them to Lua; the generated programs run on LuaJIT. LuaFun and Lua
Lanes are pinned by Nix, with local Teal declaration files describing the
external module APIs used by the build. Lua Lanes runs isolated Agda workers,
and the worker driver handles both failed process exit statuses and lane-level
errors returned by `:join()`. The LuaFun source audit bans
only the contraction/repetition family `duplicate`, `replicate`, `xrepeat`,
and `cycle`. Operations such as `split`, `span`, `partition`, `tabulate`,
`zeros`, `ones`, and random generators are outside that ban.

CI checks Teal types, Agda, Agda2HS extraction, GHC typechecking, the LuaFun
source audit, the RUSS inventory, and the static Pages artifact. The small
Bool definitions in Agda are executable sanity checks, not a substitute for
a comprehensive test suite.


## Build performance diagnosis

The first cold-cache run, [#45549279892](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45549279892), failed after 14 minutes while Nix compiled Agda 2.9.0. The build log reached module 431 of 491 before `Setup build` was killed with exit status 137. That is a SIGKILL. Runner memory pressure is the leading explanation, although the log contains no kernel OOM record.

The follow-up run, [#45575526704](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45575526704), completed the Agda 2.9.0 and Agda2Hs 1.5 toolchain builds, then stopped at `tl check .ci/teal/palette_css.tl`. The initial diagnosis incorrectly said no LuaFun declaration file existed. It does exist at `.ci/teal/fun.d.tl`, and it describes the `foldl`, `totable`, `map`, `range`, and `filter` operations used by the palette generator.

The actual first problem was Teal's module search path: CI invoked `tl check` and `tl gen` without adding `.ci/teal` as an include directory. Teal therefore could not discover `fun.d.tl` for `require("fun")`. The CI driver now checks that `.ci/teal/fun.d.tl` exists and passes `-I .ci/teal` to every Teal source check and generated-runtime compilation. Teal documents `-I / --include-dir` as the option that prepends a directory to the module search path for both `check` and `gen` ([compiler options](https://teal-language.org/book/latest/compiler_options.html)); its [declaration-file guide](https://teal-language.org/book/latest/declaration_files.html) confirms that `.d.tl` modules supply type information for ordinary `require` calls.

The next run, [#45749219870](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45749219870), found a syntax error inside that declaration: `.ci/teal/fun.d.tl:4:20: cannot declare type arguments twice in type declaration`. The declaration used `local type Iterator<T> = record<T>`, which declares the same type parameter on both the alias and the generic record constructor. Teal's [generic-record syntax](https://teal-language.org/book/latest/generics.html) puts the parameter on the record constructor, so the declaration is now `local type Iterator = record<T>`. The seven later errors saying `fun` had type `boolean` were cascading errors after Teal rejected the declaration file; they were not seven separate LuaFun API errors.

The regression check is the existing `tl check -I .ci/teal .ci/teal/palette_css.tl`: it loads the real declaration through `require("fun")` and type-checks all five LuaFun operations used by the palette generator. Runtime generation also receives the same include directory. This patch keeps strict type checking enabled and makes no changes to LuaFun runtime behavior.

The next run, [#45751047057](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45751047057), passed the LuaFun declaration and palette-generator checks, then failed at `.ci/teal/parallel_agda.tl`: there was no declaration for the pinned Lua Lanes module, so Teal could not type-check `lanes.gen` or the handle's `:join()`. The new `.ci/teal/lanes.d.tl` models the pinned Lanes 3.17.2 API, including `configure()`, `gen()` returning a callable function, and `:join()` returning worker results or `nil, error`. The declaration is based on the pinned upstream [Lanes source](https://github.com/LuaLanes/lanes/blob/6775bd90b1eac57a27856382f8e7035c2202a08b/src/lanes.lua). The worker driver handles lane-level errors explicitly. Teal records are nominal types, so `WorkerResult` and `LaneHandle` are nested in the exported `Lanes` record; the worker uses those exact exported types instead of redeclaring incompatible local records. CI type-checks the parallel worker against that declaration.

The Nix cache save step ran, but its 8 GiB garbage-collection pass removed completed `Agda-2.9.0`, `agda2hs-1.5`, and GHC environment store paths after `nix develop` released its temporary root. The workflow now builds the `agda-ci` devShell with an out-link under `.cache/nix-roots` before entering the shell. That link keeps the shell dependency closure rooted during cache save. The cache key uses a `gcroot-v2` suffix, so the old cache cannot count as an exact hit. The GC ceiling is 12 GiB.

A MAlonzo reset has no bearing on this path. CI invokes `agda2hs-agda --disable-backend` for typechecking and calls Agda2HS for extraction. Neither step invokes Agda's `--compile` backend. Removing `MAlonzo/` cannot affect the failing Teal check, and deleting cached `.agdai` interfaces would make later Agda checks slower.

A reinstall or blind Agda2HS/Agda upgrade has no support in the current evidence. The latest run built the pinned Agda 2.9.0 and Agda2Hs 1.5 toolchain. Keep those pins until the workflow reaches the learner checks and produces evidence of a compiler or compatibility problem.

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
