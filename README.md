# Deep Watkins Monoid LSTM

A single-file Agda2HS learner kernel, with a fixed-point runtime boundary and erased proof support.

> **Development status:** the repository is in an active refactor. The canonical Agda module now contains the confined proof surface, an erased-length vector, and a Q12.20 integer arithmetic boundary. The complete recurrent learner and its training algorithm are still under development. This repository does not yet claim a verified GRU, CHAD transform, FQF-SARSA update, actor, or optimizer.

## Design goals

- Keep runtime learner semantics in `FullCoupled/CanonicalLearnerMonolith.agda`.
- Use Agda for types, total definitions, erased invariants, and proof structure.
- Extract Haskell with the pinned Agda2HS toolchain.
- Keep runtime numeric values in signed Q12.20 backed by `Data.Int.Int32`.
- Widen products and division numerators to `Int64`.
- Round fixed-point results to nearest, ties to even.
- Saturate results at the `Int32` bounds.
- Keep `Float` and `Double` out of the learner source and extracted learner module.
- Keep IO, pointer, callback, and concurrency adapters outside the pure learner.

## Current module

`FullCoupled/CanonicalLearnerMonolith.agda` is the canonical implementation file.

It currently contains:

| Component | Current state |
| --- | --- |
| Narrow proof imports | Implemented |
| Erased `S0` witness packaging | Implemented |
| Equality and relation support | Implemented |
| Erased-length `Vec` | Implemented |
| Q12.20 `Int32` representation | Implemented |
| Saturating add and subtract | Implemented |
| Q12.20 multiply with ties-to-even rounding | Implemented |
| Saturating negate and absolute value | Implemented |
| Q12.20 division with explicit divide-by-zero result | Implemented |
| Quantmoid4 integer kernel and smooth CHAD shadow | Planned |
| State-independent-candidate GRU | Planned |
| Three-step sampled SARSA | Planned |
| 16-fraction FQF and quantile-Huber loss | Planned |
| Actor-only factorized NoisyNet | Planned |
| Munchausen reward shaping | Planned |
| ObGD update and its vector-gradient bound | Planned |
| End-to-end CHAD and runtime parity proofs | Planned |

The foreign Haskell arithmetic functions are trusted postulates from Agda's point of view. The Agda type checker checks their types, not their runtime bodies. Add reference tests and extracted-Haskell parity checks before treating these functions as verified.

## Fixed-point format

Q12.20 stores a signed integer `raw` with scale `2^20`.

```text
value = raw / 1,048,576
raw range = [-2,147,483,648, 2,147,483,647]
value range = [-2,048, 2,047.99999904632568359375]
```

Addition and subtraction widen to `Int64`, then saturate to `Int32`.

Multiplication computes the `Int64` product, divides by `2^20) using round-to-nearest, ties-to-even, then saturates.

Division scales the numerator by `2^20), applies the same rounding rule, and saturates. Division by zero returns `Q20DivByZero`.

## Import policy

The canonical module uses the small Agda2HS and Agda proof surface needed by this pure learner:

- `Agda.Primitive` supplies universe levels for erased proof packaging.
- `Agda.Builtin.Equality` supplies propositional equality.
- `Haskell.Prim` supplies the empty type used by relation proofs.
- `Haskell.Prim.Tuple` supplies product types.
- `Data.Int.Int32` and `Data.Int.Int64` enter only through the narrow `FOREIGN AGDA2HS` block.

The erased `S0`, equality helpers, and relation support follow the relevant patterns in Viktor Csimma's [Agdalache](https://github.com/viktorcsimma/agdalache) source. The learner does not depend on Agdalache as a package, and its GUI-specific runtime adapters are not part of this module.

### Why the canonical module omits Haskell.Prelude

The omission is about import confinement and the no-floating-point contract. It is **not** based on a claim that Viktor Csimma says `Haskell.Prelude` is slow.

Csimma's Agdalache examples use `Haskell.Prelude` in application state, interaction, and foreign-boundary modules. The pinned Agda2HS `Haskell.Prelude` itself re-exports a broad set of modules, including `Haskell.Prim.Double`, `Haskell.Prim.IO`, and numeric classes with a `Double` instance. That surface is broader than this learner needs.

Agda2HS documentation says unused imports are omitted from generated Haskell. Therefore, importing the broad Prelude does not by itself establish a runtime performance penalty. A broad Agda import can still enlarge the type-checking dependency graph, but this repository has no benchmark showing that `Haskell.Prelude` is slow.

The canonical module therefore uses selected proof imports and a small fixed-width FFI boundary. It does not import Csimma's `IORef`, `Ptr`, `StablePtr`, C-type, `Storable`, `MVar`, `CFuture`, GHC-concurrency, or platform adapters. Those modules solve mutable GUI state and C/C++ callback integration. The learner has no such boundary.

## Learner specification

The planned learner keeps the runtime model integer-only.

### Recurrent model

- Use a state-independent-candidate GRU.
- Compute the candidate from the current feature projection only.
- Use a shifted and rescaled softsign update gate in `[0, 1]).
- Mix the previous hidden state and candidate with complementary gate weights.
- Apply the specified outer softsign.
- Differentiate a separate C1 dyadic shadow with CHAD. The rounded integer forward kernel is discrete and is not itself C1.

### Critic and return

- Use three-step sampled on-policy SARSA.
- Set `gamma = 0.99` and `lambda = 0`.
- Bootstrap with the action sampled by the behavior policy at the third step.
- Shorten the return at earlier termination.
- Keep samples chronological. Do not shuffle or decorrelate replay sequences.
- Use 16 learned FQF quantile fractions and 16 quantile values per action.
- Train quantile values with quantile-Huber loss.

SARSA avoids the `max_a Q(s,a)` selection step in the bootstrap. This reduces the classic maximization-bias mechanism in Q-learning. It does not guarantee unbiased estimates.

### Actor and exploration

- Keep the critic deterministic.
- Apply factorized NoisyNet only to the actor policy head.
- Generate noise with integer-only quantized distributions and explicit range bounds.
- Use integer Q4-softmax with temperature `tau = 1/8`.
- Do not add epsilon-greedy exploration.
- Use canonical Munchausen shaping:
  `rM = r + alpha * tau * log(pi(a|s))`.
- Use `alpha = 1/16` and `tau = 1/8`.
- Approximate log-probabilities with a bounded integer lookup or dyadic kernel.

Munchausen shaping is policy-dependent reward shaping. It is not a general overestimation correction. Bound the error from the integer log and softmax approximations separately.

### Optimizer and differentiation

- Use ObGD without Adamax or momentum.
- Justify its effective-step bound for the aggregate quantile-Huber gradient.
- Use sparse cotangent products and state-passing accumulation.
- Prove the primal/VJP relation for the smooth dyadic shadow.
- Prove the three-step cotangent accumulation bounds.
- State the cost model and prove the claimed bound.
- Separate shadow correctness from fixed-point quantization error.

## Viktor Csimma import inventory

The inventory below distinguishes the reusable proof pattern from adapters that belong to other applications.

| Csimma source family | Learner decision |
| --- | --- |
| `Tool.ErasureProduct` | Reuse the erased `S0` pattern in the canonical file. |
| `Tool.PropositionalEquality` | Reuse the minimal erased equality helpers. |
| `Tool.Relation` | Reuse the small relation vocabulary and empty-type contradiction. |
| `Haskell.Prelude` | Excluded from the canonical import surface because it exposes unused floating-point and IO APIs. |
| `Haskell.Data.IORef` | Excluded. The learner kernel is pure. |
| `Haskell.Foreign.Ptr` | Excluded. No pointer-valued learner interface exists. |
| `Haskell.Foreign.StablePtr` | Excluded. No stable-pointer lifetime exists. |
| `Haskell.Foreign.C.Types` | Excluded. The learner does not expose a C ABI. |
| `Haskell.Foreign.Storable` | Excluded. No pointer marshalling exists. |
| `Tool.Foreign` | Excluded. No C/C++ function adapter is required. |
| `Haskell.Control.Concurrent.MVar` | Excluded. No shared mutable state is required. |
| `Haskell.Control.Concurrent.CFuture` | Excluded. No asynchronous C callback exists. |
| `Haskell.GHC.Conc` | Excluded. Runtime concurrency is outside the learner. |
| `Platform.Posix` and `Platform.Win32` | Excluded. The learner is platform-independent. |

“Full coverage” means every import family has an explicit decision. It does not mean importing modules whose runtime responsibilities do not exist in this project.

## Build and verification

The Nix flake pins Agda2HS, Agda, GHC, and the Agda2HS base library.

Run the canonical Agda type check:

```sh
nix develop --quiet .#agda-ci -c agda2hs-agda --trace-imports=0 -i . FullCoupled/CanonicalLearnerMonolith.agda
```

Run Agda2HS extraction and inspect the generated Haskell:

```sh
nix develop --quiet .#agda-ci -c agda2hs FullCoupled/CanonicalLearnerMonolith.agda -o build/agda2hs
```

Run the repository's full CI lane:

```sh
nix develop --quiet .#agda-ci -c fennel .ci/fennel/ci.fnl All
```

The CI lane checks the canonical Agda module, extracts it, checks the theorem monolith, audits RUSS trust declarations, and renders the static Pages site.

Before merging the learner, add and run tests for:

1. Q12.20 extrema, saturating arithmetic, negative rounding ties, and division by zero.
2. Quantmoid4 knots, monotonicity, saturation, and shadow discrepancy.
3. GRU candidate independence, gate range, and CHAD primal/VJP correspondence.
4. Three-step SARSA termination, truncation, and sampled-action bootstrap.
5. FQF fraction positivity, strict ordering, normalization, and quantile-Huber gradients.
6. Actor-noise isolation from the deterministic critic.
7. Munchausen sign and integer log approximation bounds.
8. ObGD's vector-gradient step bound.
9. Extracted-Haskell scans for floating-point types, literals, imports, and conversions.

A successful type check or extraction does not prove the FFI arithmetic bodies or the full learner correct.

## Repository layout

```text
.
├── .ci/
│   ├── agda/
│   │   ├── agda2hs.yaml
│   │   └── global-options.txt
│   └── fennel/
│       ├── ci.fnl
│       ├── pages.fnl
│       ├── palette_css.fnl
│       └── russ_audit.fnl
├── .github/workflows/github-pages.yml
├── FullCoupled/
│   ├── CanonicalLearnerMonolith.agda
│   └── TheoremsMonolith.agda
├── site/site.less
├── flake.nix
├── index.html
└── README.md
```

## License

See [LICENSE](LICENSE).
