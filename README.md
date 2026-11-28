# SpecSmac3Agda

`FullCoupled/CanonicalLearnerMonolith.agda` is the repository's sole learner module and the only canonical learner implementation. There is no parallel, legacy, or secondary learner source. The theorem module and the local integer/bit modules support verification and compilation; none defines another learner.

Agda 2.9 source for a bounded type-code calculus, an affine combinator core, a micro-Haskell heap-spine evaluator, and a fixed-point V73 champion model.

The canonical module is `FullCoupled/CanonicalLearnerMonolith.agda`. Its module name matches that path. The replacement's declarations and computational definitions are kept intact; the module header is the only source-level adjustment made for the canonical path.

## Type codes and erased assumptions

The type-code language represents integers, de Bruijn-style variables, arrows, products, and bounded universal quantification. `BoundedDecodeType` and its decoding equations are postulated in the erased fragment and installed as rewrite rules.

The erased section also declares a quantum-extended universal enumerator, a parametric-index equation, and an erased Markov principle. These are explicit assumptions in the source, not theorems derived by the executable model.

## Affine core and evaluator

`LinearType` is indexed by positive and negative polarity. `LinearContext` records focused resources, `DisjointContextSplit` describes context partition, and `AffineProof` provides variable, weakening, and composition constructors.

The executable combinator layer defines B, C, I, K, P, and A functions, stack operations, and a fuel-bounded heap-spine evaluator for a small combinator language. Its evaluator reduces selected combinator applications and integer addition, multiplication, and comparison.

## V73 fixed-point model

`MinimaxChampionHyperParameters` carries integer-scaled parameters. The declared unit is (2^{26}), with a 26-bit fractional shift. Arithmetic uses the imported signed `Int` operations and explicit shift counts.

The model includes Quantmoid4 and its smooth-shadow derivative, a Gaussian-error-linear-unit approximation, fixed-point convolution stages, gate and cell updates, dueling quantile heads, factorized noise inputs, a Barrett-style streaming optimizer step, and the V73 `stepMinimaxChampion` transition. The transition's action/value calculation uses the CancelZeroMeanTop1 expected-SARSA expression and IQN13 quantile modulation.

The file also includes small Pathfinder 2e Remaster modifier and degree-of-success evaluators. These functions do not constitute a complete rules engine.

## Theorem module

`FullCoupled/TheoremsMonolith.agda` remains under Agda's `--safe` profile. It enables `--guardedness` locally for delayed coinductive structures. The covariance orbit is defined with an explicit delayed tail, and finite-prefix folds recurse on their natural-number bound.

## Build and verification

The Nix development shell pins Agda 2.9, Agda2HS, Teal, LuaJIT, and LuaFun. Teal programs drive isolated Agda checks, source guards, RUSS inventory, and static Pages rendering. Agda2HS extracts the canonical module, and GHC type-checks the generated Haskell.

The RUSS output is a lexical inventory of source markers. It is not a proof certificate. A passing CI run establishes the declared source and compiler checks; it does not establish numerical accuracy, learning performance, or the soundness of the explicitly postulated assumptions.
