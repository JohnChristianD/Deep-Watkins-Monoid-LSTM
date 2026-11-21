# Deep Watkins Monoid LSTM

An Agda2HS research project for a proof-oriented, fixed-point recurrent reinforcement-learning kernel. Agda owns the typed learner semantics; Agda2HS extracts the executable Haskell boundary.

## Status

**Active refactor; not a completed learner.** The canonical module currently provides:

- erased proof packaging and equality/relation support;
- an erased-length vector with map and zip;
- an opaque Q12.20 wrapper backed by signed Int32;
- saturating addition, subtraction, negation, and absolute value;
- Q12.20 multiplication and division with round-to-nearest, ties-to-even;
- an explicit divide-by-zero result.

The recurrent GRU, Quantmoid4, CHAD transform, FQF quantile learner, three-step SARSA, actor, Munchausen shaping, ObGD optimizer, end-to-end proofs, and runtime tests remain unimplemented. They must not be described as completed features.

The foreign arithmetic declarations are trusted postulates from Agda's perspective. Agda checks their types; it does not prove the Haskell bodies correct. The fixed-point implementation still needs executable reference tests and extracted-Haskell parity checks.

## Canonical source and numeric boundary

All runtime learner work belongs in:

    FullCoupled/CanonicalLearnerMonolith.agda

The theorem file remains a separate verification target:

    FullCoupled/TheoremsMonolith.agda

The intended runtime representation is signed Q12.20:

- scale: 2^20 = 1,048,576;
- raw storage: signed 32-bit integer;
- representable interval: [-2048, 2047.99999904632568359375];
- widened intermediates: signed 64-bit integer;
- narrowing: explicit saturation;
- multiplication and division: round-to-nearest, ties-to-even;
- division by zero: represented by Q20DivByZero.

No floating-point values belong in the learner runtime. This is a boundary requirement, not a claim that every library in the development toolchain must be free of floating-point support.

## Agda2HS import policy

The canonical Agda file follows the standard Agda2HS base-library convention and explicitly opens:

    open import Haskell.Prelude public

It also imports `Agda.Primitive` for universe levels. The Prelude re-exports the base definitions used by this module, including propositional equality, builtin `Nat`, products, and primitive proof types. Separate imports of `Agda.Builtin.Equality`, `Agda.Builtin.Nat`, `Haskell.Prim`, and `Haskell.Prim.Tuple` are redundant and have been removed.

### Why Haskell.Prelude belongs here

Viktor Csimma's Agdalache/Agda2HS examples follow the normal Agda2HS approach: use `Haskell.Prelude` as the shared Agda/Haskell sublanguage. Agda2HS documentation describes its base Prelude as the intended companion library. This repository now follows that convention.

The Prelude exposes a broad set of Haskell facilities, including numeric and IO-related definitions. Their presence in the Agda import scope does not mean the learner evaluates floating-point values or performs IO. The learner's numeric representation remains signed Q12.20 over `Int32`, with widened `Int64` intermediates. No `Double`, floating literal, float conversion, or IO operation is used by the canonical learner. The extraction configuration records the repository's Prelude policy in `.ci/agda/agda2hs.yaml`.

There is no evidence that importing `Haskell.Prelude` makes generated learner arithmetic slower. The previous decision to omit it departed from the normal Agda2HS convention and is corrected here.

### Agda.Builtin.Nat is compatible and not a Peano runtime penalty

`Haskell.Prelude` re-exports `Nat`, `zero`, and `suc` from `Agda.Builtin.Nat`. This is compatible with Agda2HS: the Agda2HS base library is built around Agda's builtin Nat and maps it to Haskell's `Numeric.Natural.Natural`. The extracted Haskell representation is an arbitrary-precision natural-number type, not a linked Peano constructor chain.

Agda's builtin Nat also receives special treatment by the Agda type checker/compiler for efficient arithmetic. Here, Nat is used only as the length index of `Vec`, and that index is explicitly erased with `@0`. The vector's runtime representation therefore carries no Nat length and performs no runtime Peano traversal for length bookkeeping. Import it through `Haskell.Prelude`, rather than opening the builtin module a second time.

For fixed-point learner arithmetic, Nat is not the numeric representation: signed values remain `Int32` and widened intermediates remain `Int64`.

### Relevant Csimma module families

Faithfulness means following Csimma's Agda2HS conventions and importing modules for responsibilities the code actually uses. It does not mean importing every GUI integration module into a pure learner.

| Module family | Decision |
| --- | --- |
| `Haskell.Prelude` | Imported; standard Agda2HS programming surface. |
| `Haskell.Prim`, `Haskell.Prim.Tuple` | Re-exported through Prelude; no duplicate direct imports. |
| `Agda.Primitive` | Direct import for universe levels. |
| `Haskell.Data.IORef` | Not used; learner kernel remains pure. |
| `Haskell.Foreign.Ptr`, `StablePtr`, `Storable` | Not used; no pointer lifetime or marshalling API. |
| `Haskell.Foreign.C.Types`, `Tool.Foreign` | Not used; fixed-width arithmetic primitives are supplied in the narrow Agda2HS foreign block. |
| `Haskell.Control.Concurrent.MVar`, `CFuture`, `Haskell.GHC.Conc` | Not used by the pure learner. |
| `Platform.Posix`, `Platform.Win32` | Not used; no platform-specific learner interface. |
| `Tool.ErasureProduct`, `Tool.PropositionalEquality`, `Tool.Relation` | Relevant erased-proof and relation patterns are represented in the canonical monolith; GUI/backend application modules are not runtime dependencies. |

Agdalache is a C++ Qt application toolkit around an Agda/Agda2HS backend; Agda2HS itself extracts readable Haskell. It is not a C++/OCaml/Rocq extraction backend. C++ integration belongs at an application adapter; the canonical learner source targets Agda2HS/Haskell.

## Planned learner contract

The intended implementation, once completed and proved, has these constraints.

### Recurrent core

- State-independent candidate: current feature projection only, with no recurrent-state term in the candidate.
- Shifted/rescaled softsign update gate in [0,1].
- Convex mix of previous hidden state and candidate, followed by the required outer softsign.
- Integer Quantmoid4 forward kernel with a separately specified continuous dyadic shadow for CHAD. The rounded integer forward function is discrete; it is not itself C1.

### Critic and return

- Three-step sampled on-policy SARSA, gamma = 0.99, lambda = 0.
- Bootstrap from the action sampled at the third step; shorten the return on earlier termination.
- Preserve chronological contiguous samples. No replay shuffling or decorrelation.
- Sixteen learned FQF fractions and sixteen quantile values per action, trained with quantile-Huber loss.
- No max-Q bootstrap, Double-Q target, dueling decomposition, ensemble, target network, or categorical five-bin projection in this iteration.

SARSA removes the max_a Q(s,a) selection from the bootstrap and therefore avoids that particular maximization-bias mechanism of Q-learning. It does not guarantee unbiased value estimates.

### Actor and reward shaping

- Factorized NoisyNet belongs to the actor policy head only. The critic and recurrent state remain deterministic.
- Integer Q4-softmax with temperature tau = 1/8; no epsilon-greedy branch.
- Canonical Munchausen shaping: rM = r + alpha * tau * log(pi(a|s)), with alpha = 1/16 and tau = 1/8.
- Integer log and softmax approximation errors require explicit bounds.

Munchausen shaping is policy-dependent reward shaping, not a universal overestimation correction.

### Differentiation and optimization

- Sparse cotangent products and state-passing accumulation.
- CHAD VJP derived from the declared smooth dyadic shadow, not from a discontinuous rounded integer map.
- Compose the fixed three-step pullback directly; reserve iterative CHAD for genuinely variable-length control flow.
- ObGD without Adamax or momentum; prove the effective-step bound for the aggregate quantile-Huber gradient.
- Prove primal/VJP simulation, cotangent laws, three-step overflow bounds, and the stated cost bound.

## Development environment and parallel typechecking

The agda-ci Nix development shell provides the pinned Agda2HS/Agda toolchain, GHC, Fennel, LuaJIT, and LuaRocks. On shell entry, LuaRocks installs the pinned lanes and Lua Fun (fun) rocks into the ignored project-local .luarocks/ tree. Lanes runs the two independent Agda typechecks concurrently; Lua Fun supplies the functional iterator used to construct the worker jobs.

The parallel checker gives each Agda invocation a separate temporary source workspace and uses --local-interfaces. This isolates local .agdai writes between workers. The worker count is two; Nix and Make are also configured for two build jobs. Actual CPU availability remains controlled by the host.

Typecheck both Agda monoliths concurrently:

    nix develop --quiet .#agda-ci -c fennel .ci/fennel/parallel-agda.fnl

Run the full CI lane:

    nix develop --quiet .#agda-ci -c fennel .ci/fennel/ci.fnl All

The full lane typechecks both Agda files concurrently, extracts the canonical Agda module, checks the RUSS trust inventory, and renders the static Pages artifact.

## Verification still required

Before treating the learner as complete, add and run:

1. Q12.20 extrema, saturation, negative rounding ties, and divide-by-zero tests.
2. Quantmoid4 knot, monotonicity, saturation, and shadow-discrepancy tests.
3. GRU candidate-independence, gate-range, and CHAD primal/VJP checks.
4. Three-step SARSA terminal, truncation, and sampled-action-bootstrap tests.
5. FQF fraction positivity, strict ordering, normalization, and quantile-Huber gradient checks.
6. Actor-noise isolation from critic and recurrent state.
7. Munchausen sign and integer-log error bounds.
8. ObGD vector-gradient step-bound proof.
9. Extracted-Haskell scans for floating-point types, literals, imports, and conversions.
10. End-to-end parity checks for the trusted fixed-point Haskell primitives.

A successful Agda typecheck or Agda2HS extraction is necessary but does not establish the correctness of foreign arithmetic bodies or the missing learner.

## Repository map

    .
    ├── .ci/
    │   ├── agda/
    │   │   ├── agda2hs.yaml
    │   │   └── global-options.txt
    │   └── fennel/
    │       ├── ci.fnl
    │       ├── parallel-agda.fnl
    │       ├── pages.fnl
    │       ├── palette_css.fnl
    │       └── russ_audit.fnl
    ├── .github/workflows/github-pages.yml
    ├── FullCoupled/
    │   ├── CanonicalLearnerMonolith.agda
    │   └── TheoremsMonolith.agda
    ├── flake.nix
    ├── index.html
    ├── site.css
    └── README.md

## License

See LICENSE.
