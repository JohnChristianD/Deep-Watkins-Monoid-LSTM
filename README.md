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

The canonical Agda file currently imports:

| Import | Purpose |
| --- | --- |
| Agda.Primitive | Universe levels for erased proof packaging. |
| Agda.Builtin.Equality | Propositional equality and its constructor. |
| Agda.Builtin.Nat | Length index and constructors for erased-length vectors. |
| Haskell.Prim | Empty type used by the relation contradiction. |
| Haskell.Prim.Tuple | Product type used by the pair alias. |

The two Haskell.* modules are Agda2HS base-library imports reused from Viktor Csimma's Agda2HS ecosystem. The other imports are Agda built-ins. The foreign Haskell block names Data.Int.Int32 and Data.Int.Int64 and defines the narrow arithmetic primitives used by this module.

### Why Haskell.Prelude is omitted

**Import confinement and floating-point exposure—not a measured runtime-speed issue.**

Viktor Csimma's Agdalache application modules do use Haskell.Prelude; its presence in those examples is not evidence that it is slow. In the pinned Agda2HS base library, the Prelude is a broad convenience surface that re-exports general-purpose primitives, including floating-point and IO-related facilities. The canonical learner needs only a handful of proof and product primitives, so importing the whole Prelude would widen its source-level dependency surface without supplying a needed operation.

Agda2HS extraction omits unused imported Haskell entities from generated output. Consequently, a broad Prelude import does not, by itself, prove slower generated code. A broad import can affect Agda's dependency/typechecking surface, but this repository has no benchmark establishing a Prelude slowdown. The project makes no such performance claim and does not attribute one to Csimma.

The policy is to reuse **all relevant** Csimma Agda2HS patterns, not indiscriminately import every module used by his GUI/FFI applications:

| Csimma module family | Decision for this pure learner |
| --- | --- |
| Haskell.Prim | Import the empty type needed by relation proofs. |
| Haskell.Prim.Tuple | Import products where the learner uses them. |
| Haskell.Prelude | Omit; current code needs no broad Prelude re-export. |
| Haskell.Data.IORef | Omit; no mutable IO reference in the pure kernel. |
| Haskell.Foreign.Ptr, StablePtr, Storable | Omit; no pointer lifetime or marshalling boundary. |
| Haskell.Foreign.C.Types, Tool.Foreign | Omit; no C ABI adapter is declared. |
| Haskell.Control.Concurrent.MVar, CFuture, Haskell.GHC.Conc | Omit; learner state is not shared mutable concurrent state. |
| Platform.Posix, Platform.Win32 | Omit; the learner kernel is platform-independent. |
| Tool.ErasureProduct, Tool.PropositionalEquality, Tool.Relation | Reuse relevant definitions/patterns in the canonical monolith; do not add application modules as runtime dependencies. |

This is a complete decision policy, not a maximal import count. Add a module only when the canonical source actually uses the responsibility it provides.

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

The agda-ci Nix development shell provides the pinned Agda2HS/Agda toolchain, GHC, Fennel, LuaJIT, and LuaRocks. On shell entry, LuaRocks installs pinned lanes and luafun rocks into the ignored project-local .luarocks/ tree. Lanes runs the two independent Agda typechecks concurrently; LuaFun supplies the functional iterator used to construct the worker jobs.

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
