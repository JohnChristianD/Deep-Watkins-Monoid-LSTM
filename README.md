# Deep Watkins RNN

Agda-first Q8.24 recurrent, distributional reinforcement-learning prototype.
The canonical learner is `FullCoupled/CanonicalLearnerMonolith.agda`.
This README is the repository's only project documentation.

The public Agda imports retain the Prelude, integer, bit-shift, and rewrite APIs while hiding Prelude's bottom and tuple/product names so the learner's domain operators remain distinct:

```agda
open import Haskell.Prelude public hiding (⊥; _×_; _×_×_; _,_)
open import Haskell.Data.Int public
open import Haskell.Data.Bits public
open import Agda.Builtin.Equality.Rewrite public
```

Q8.24 values use the base library's signed 64-bit `Int` carrier. `qFrom64`
saturates narrowed results to the signed 32-bit Q8.24 range, while intermediate
arithmetic remains in the 64-bit carrier. The local `Haskell.Data.Int` module
provides signed quotient with truncation toward zero; `Haskell.Data.Bits`
provides left and arithmetic-right shifts with natural-number shift counts.
Proof checks cover quotient signs and shifts at and beyond the carrier width.
Agda2HS extracts the Haskell-compatible declarations; GHC checks the extracted
module in CI.

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


## CI diagnosis and verification

CI runs quick checks before the expensive Agda/GHC work. The preflight type-checks every Teal source, audits repository constraints and the learner's required symbols, generates and type-checks the RUSS inventory, and renders the static Pages site. Only after those checks pass does CI start the parallel Agda workers, extract Haskell with Agda2HS, and type-check the generated module with GHC. Failures in Teal, RUSS, or Pages therefore return before the long compiler stages.

Recent failures exposed distinct problems:

- Cold-cache run [#45549279892](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45549279892) was killed with exit status 137 while Nix compiled Agda 2.9.0, at module 431 of 491. Runner memory pressure is the leading explanation; the log has no kernel OOM record.

- Run [#45575526704](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45575526704) built Agda 2.9.0 and Agda2Hs 1.5, then Teal could not resolve require(fun). CI now passes the .ci/teal directory to both tl check and tl gen.

- Run [#45749219870](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45749219870) exposed a duplicate generic parameter in fun.d.tl. The alias now uses Teal's local type Iterator = record<T> form.

- Run [#45751047057](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45751047057) found that the pinned Lua Lanes module had no Teal declaration. lanes.d.tl now describes the pinned configure, gen, and join API.

- Run [#45760204352](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45760204352) showed that Teal records are nominal: the worker and declaration had separately defined result and handle types. Both sides now refer to the nested types exported by Lanes. After that correction, the parallel worker type-check passed and the RUSS audit exposed a separate contract error: string.gsub returns a string and a replacement count. The trim helper now binds the string result before returning it. Runtime assertions cover whitespace trimming and postulate-block counting. Run [#45786928134](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45786928134) then showed a runtime path bug: workers changed into their workspace before redirecting output to a repository-relative log path. Each log now lives inside its worker workspace, so the redirection and later log read address the same file. The driver also initializes the shared Agda base-library and primitive-data caches once before launching concurrent workers. Run [#45788120741](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45788120741) then confirmed Agda 2.9.0 rejects the removed `--local-interfaces` option. Each worker already runs from its own workspace, which isolates Agda's default interface cache, so the obsolete flag has been removed.

The Teal declarations describe the pinned LuaFun and Lua Lanes APIs. The Lanes declaration follows the pinned [3.17.2 source](https://github.com/LuaLanes/lanes/blob/6775bd90b1eac57a27856382f8e7035c2202a08b). The LuaFun source audit bans only duplicate, replicate, xrepeat, and cycle; it does not ban operations such as split, span, partition, tabulate, zeros, ones, or random generators.

Runs [#45898705172](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45898705172) and [#45899659770](https://github.com/JohnChristianD/Deep-SARSA-GRU/actions/runs/45899659770) exposed a compiler-boundary problem: command-wide `--rewriting` and `--type-in-type` options leaked into imported modules that carry Agda's `--safe` contract. Both options are now declared only in the learner module's `OPTIONS` pragma. The global options file and wrapper-level option injection have been removed, so each module is checked under its own declared profile.

The theorem module remains `--safe` and enables `--guardedness` locally because Agda's built-in delayed-coinduction module requires that option at the import boundary. Its conaturals, conatural streams, and Codyadic digit streams use `∞`, `♯`, and `♭`, so recursive tails are explicit and checked for productivity. The option stays confined to this theorem module; it is not injected into the learner's compiler profile. Finite approximation and prefix folds remain structurally recursive on their explicit bounds. CI preflight checks the option boundary and delayed-tail definitions before starting Agda.

The Nix store cache previously garbage-collected completed compiler dependencies after nix develop released its temporary root. CI now builds the agda-ci devShell through an out-link under .cache/nix-roots before entering the shell, keeping the dependency closure reachable during cache save. Store hardlink optimization is disabled for cache compatibility, and the GC ceiling is 12 GiB.

CI invokes agda2hs-agda --disable-backend for Agda checking; it does not invoke Agda's MAlonzo compilation backend. Deleting MAlonzo/ or cached .agdai interfaces cannot fix a Teal failure and would discard useful Agda cache state. Keep the Agda 2.9.0 and Agda2Hs 1.5 pins until a later compiler stage supplies evidence of a compatibility issue.

A green build verifies source and compiler contracts. It does not establish numerical or learning correctness. The learner still needs reference tests for Q8.24 arithmetic, Quantmoid4 and cosine approximations, IDBD projection, and NoisyNet parity; transition tests for quantile weighting, action alignment, critic alternation, and terminal targets; finite-difference checks for recurrent and critic gradients; an affine-use proof; and end-to-end environment evaluation. The project remains a prototype until those checks pass.
