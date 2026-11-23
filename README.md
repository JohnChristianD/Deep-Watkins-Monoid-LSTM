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
for the SARSA target. The action-head dimensions are represented as ordinary
lists at this stage; callers must supply matching non-empty actor and critic
weight lists.

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

## LuaFun, YueScript, and Lanes

The build and CI tools are YueScript compiled for Lua 5.1 and run by LuaJIT.
YueScript is installed with LuaRocks into the project-local `.luarocks` tree.
Fennel is no longer part of the build.

LuaFun represents iterators as generator/parameter/state triples. Its
`map`, `filter`, `zip`, `chain`, and `foldl` operations compose
iterators. An iterator is pure only when its generator is deterministic for a
given parameter/state pair and does not mutate them. LuaFun does not enforce
purity.

This is a compositional iterator style, not Joy/Factor's native concatenative
stack language. Joy/Factor words compose stack transformations through
juxtaposition; LuaFun composes iterator values through function calls. A
stack-effect layer could be built on LuaFun, but would be an additional
convention.

YueScript and Teal can both target Lua 5.1 output; generated module/runtime
compatibility matters more than a blanket language ranking. YueScript is the
project's source syntax. Teal can be added later for static declarations.
LuaFun transformations stay in the LuaJIT process; Lua Lanes runs the two
Agda checks concurrently using separate Lua states and OS threads, not
separate processes.

The CI caches `.luarocks` and `.cache`, so installed rocks and Agda
interfaces can be reused between runs. `.ci/yue/parallel_agda.yue` builds
two isolated persistent Agda workspaces. `AGDA_PROFILE=modules` can be set
to collect Agda's module profile.

## Verification

The CI workflow compiles every `.yue` file to Lua 5.1, runs the LuaJIT CI
driver, typechecks the two Agda modules concurrently, extracts the learner
with Agda2HS, and checks the generated Haskell with an unoptimized
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
yue --target 5.1 -o build/yue/ci.lua .ci/yue/ci.yue
yue --target 5.1 -o build/yue/parallel_agda.lua .ci/yue/parallel_agda.yue
yue --target 5.1 -o build/yue/pages.lua .ci/yue/pages.yue
yue --target 5.1 -o build/yue/palette_css.lua .ci/yue/palette_css.yue
yue --target 5.1 -o build/yue/russ_audit.lua .ci/yue/russ_audit.yue
luajit build/yue/ci.lua All
```

