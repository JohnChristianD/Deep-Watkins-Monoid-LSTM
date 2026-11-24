# Deep Watkins RNN

An Agda-first recurrent actor-critic prototype. The canonical learner is
`FullCoupled/CanonicalLearnerMonolith.agda`. Agda checks the source;
Agda2HS extracts the Haskell-compatible declarations; GHC checks the extracted
module. The learner's numeric interface uses Q8.24 values stored in Int32 and
widened Int64 intermediates.

## Current learner

The current implementation is intentionally a small scalar recurrent model.
It has one recurrent hidden feature, one actor weight per action, and one
critic weight per action. It is not a full-width vector GRU.

For observation (x_t) and previous hidden state (h_{t-1}):

```text
z_t = softsign(w_x * x_t)
g_t = hard_sigmoid(z_t + u_g * h_(t-1))
c_t = ReLU(z_t + u_c * h_(t-1))
h_t = ReLU((1 - g_t) * h_(t-1) + g_t * c_t)
```

The gate is state-dependent: it reads the previous recurrent state. ReLU is
applied to the candidate and final recurrent state. Softsign is used only in
the input feature transform. The output policy is a categorical distribution
formed from normalized positive linear preferences; the critic has one scalar
Q estimate per action.

Training uses one-step on-policy SARSA:

```text
a_t     ~ pi(. | s_t)
a_(t+1) ~ pi(. | s_(t+1))
target  = r_t                                      terminal
        = r_t + gamma * Q(s_(t+1), a_(t+1))        otherwise
```

The terminal branch does not bootstrap. The same sampled next action is used
for the SARSA target. Action heads use a non-empty paired structure: the first
action has one actor weight and one critic weight, and remaining actions are
supplied as pairs. The Agda type prevents empty heads and actor/critic length
mismatches.

FQF is postponed. DeepSets has been removed. There is no LSTM, epsilon-greedy
selector, Munchausen return, or multi-step target in this version.

## Fixed-point arithmetic

The Q8.24 scale is (2^{24} = 16,777,216). The current arithmetic layer
includes saturating narrowing, widened products, signed division, ReLU,
softsign, and a hard-sigmoid gate. Products use Int64 intermediates before
shifting back into Q8.24 Int32 values.

The learner imports `Haskell.Prelude`, `Haskell.Data.Int`, and
`Haskell.Data.Bits`. No Agda rewrite postulates or C FFI shims are required
for the current scalar kernel.

MicroHs is a separate optional C-backend route; it is not yet wired into this
flake. For a bootstrap MicroHs compiler, the relevant upstream files are:

| MicroHs source | Role |
| --- | --- |
| `generated/mhs.c` | Embedded combinator program for the compiler |
| `src/runtime/main.c` | Runtime executable entry point |
| `src/runtime/eval.c` | Combinator evaluator |
| `src/runtime/bfile.c` | Included from `eval.c`; do not compile separately |
| `src/runtime/mhsffi.h` | Runtime declarations and configuration include |
| `src/runtime/unix/config.h` | Unix runtime configuration |
| `src/runtime/*.h`, `src/runtime/unix/*.h` | Runtime headers |
| `mhs.conf.in`, `Makefile` | Build configuration and targets |

For the learner executable, MicroHs generates its own C file. That learner C
file is linked with the runtime; `generated/mhs.c` is needed to bootstrap the
compiler, not to link every learner. The upstream Makefile and
`eval.c` are authoritative about included runtime C files.
See [MicroHs](https://github.com/augustss/MicroHs),
[its Makefile](https://github.com/augustss/MicroHs/blob/master/Makefile),
[the evaluator](https://github.com/augustss/MicroHs/blob/master/src/runtime/eval.c),
and [BFILE](https://github.com/augustss/MicroHs/blob/master/src/runtime/bfile.c).

MicroHs exposes `Data.Int.Int32` and `Data.Int.Int64`; the Int32
implementation and generated C boundary still need boundary/parity tests
before treating MicroHs output as interchangeable with Agda2HS/GHC output.

## Iterative CHAD status

The recurrent cell has a local VJP for the smooth shadow of the Q8.24
operations. It differentiates the ReLU branch indicators and hard-sigmoid
piecewise slope, then propagates through the input softsign transform.

`iterativeCHAD` stores the finite primal trace, then scans it from newest to
oldest. The scan threads the recurrent-state cotangent and Int64 parameter
accumulators; it returns per-input cotangents in chronological order.
`networkSequenceVJP` connects the scan to the current recurrent weights.
`networkApplySequenceGradient` applies the resulting recurrent parameter
directions.

This is a learner-specific recurrent reverse scan, not a general CHAD
compiler. Its local cotangents are supplied by the caller; the module does
not yet derive a full sequence loss and automatically feed all actor/critic
losses into the scan. The VJP describes the smooth shadow while holding
piecewise branches fixed. It does not differentiate integer rounding,
saturation, or categorical action sampling. There is no machine-checked
derivative-correctness theorem yet.

The one-step update uses the local cell pullback directly. Sequence-level
recurrent gradients use `networkSequenceVJP` and are applied separately.
Numerical and gradient parity tests are still required.

## Selected learner redesign

The selected next architecture is documented in
[ADR 0001](docs/decisions/0001-qr64-double-online-sarsa0.md): paired live
dueling IQN32 critics, Double-SARSA action selection/evaluation, factorized
NoisyNets on critic value and advantage layers, and one-step distributional
SARSA(0) at the lambda-zero True-Online limit. It specifies UTD = 1, no
replay, no frozen target network, no actor, and no multi-step return.

The ADR also specifies a Quantmoid4-tanh forward approximation with a
separate smooth-shadow derivative, Euclidean Q-projected diagonal IDBD, and
an independent `l2_gradient_decay` term. The standard IQN cosine quantile
embedding remains cosine: replacing its periodic basis with monotone
Quantmoid4-tanh would change IQN's quantile-embedding semantics.

The current Agda module above remains the earlier scalar actor-critic
implementation with softsign, categorical action selection, scalar Q heads,
and max-gradient-based updates. It does not yet implement IQN32, the paired
online critics, NoisyNets, projected IDBD, or the new affine transition
discipline. The ADR is a selected design, not a completed learner rewrite.

## LuaFun, Fennel, and Lanes

The build and CI tools are written in Fennel and execute on LuaJIT. Fennel
and the pinned LuaFun source are supplied by Nix; Lua Lanes is installed into
the project-local `.luarocks` tree. YueScript is removed from the toolchain.

LuaFun represents iterators as generator/parameter/state triples. The build
uses only basic transformations and folds: `map`, `filter`, `foldl`,
`range`, `totable`, and `any`. Code in this repository avoids iterator
cloning, repetition, partitioning, and iterator-state inspection. An iterator
is pure only when its generator is deterministic for a given parameter/state
pair and does not mutate them; LuaFun does not enforce purity. Lua's
`string.gmatch` iterator is materialized before passing its results into
LuaFun, because its single-function iterator shape differs from LuaFun's
generator/parameter/state convention.

This is a compositional iterator style, not Joy/Factor's native concatenative
stack language. Joy/Factor words compose stack transformations through
juxtaposition; LuaFun composes iterator values through function calls.

Fennel, Teal, and YueScript all target the Lua runtime, so LuaFun compatibility
is determined by the generated Lua version, module path, and host ABI—not by
a blanket restriction to one source language. Fennel's own README explicitly
promises full Lua compatibility, while Teal documents Lua 5.1–5.4 including
LuaJIT. The project standardizes on Fennel for its source syntax and keeps
LuaFun and Lanes in the same LuaJIT process. Lua Lanes runs two workers in
separate Lua states and OS threads; each worker launches its own Agda
subprocess.

The CI caches `.luarocks` and `.cache`, so Lanes and Agda interfaces can
be reused between runs. `.ci/fennel/parallel_agda.fnl` builds two isolated
persistent Agda workspaces. `AGDA_PROFILE=modules` can be set to collect
Agda's module profile.

## Verification

The CI workflow runs the Fennel driver under LuaJIT, typechecks the two
Agda modules concurrently through Lua Lanes, extracts the learner with
Agda2HS, and checks the generated Haskell with an unoptimized
`ghc-check -fno-code` wrapper. The optimized GHC wrapper remains available
for actual executable builds.

A green typecheck/extraction run does not establish numerical parity or
correctness of the smooth-shadow VJPs. Still needed:

- property tests for saturating Q8.24 arithmetic, signed division, and
  boundary behavior;
- finite-difference/reference tests for the recurrent, actor, and critic
  pullbacks;
- categorical policy probability and action-sampling tests;
- SARSA terminal/bootstrap alignment tests;
- Agda2HS/GHC and MicroHs/C runtime parity tests;
- a documented end-to-end training run.

## Local commands

```sh
nix develop --quiet .#agda-ci
fennel .ci/fennel/ci.fnl All
```

