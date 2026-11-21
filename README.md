# Deep Watkins Monoid RNN

A fixed-point recurrent reinforcement-learning experiment written in Agda and extracted through Agda2HS. The canonical Agda module owns the learner types and network semantics; a narrow Haskell foreign block supplies the fixed-width vector kernels.

## Current implementation status

The canonical module now contains a real **forward network path**:

- a state-independent affine candidate GRU with a shifted/rescaled softsign gate, convex hidden-state mix, MAD-LayerNorm, and outer softsign;
- a deterministic FQF-style critic with a fraction head, quantile-value head, and action-specific 16-quantile configuration;
- an actor-only factorized NoisyNet head, with quantized normal factors and a quantized lognormal persistence-duration table;
- integer Quantmoid4-normalized policy probabilities and discrete Gumbel-Max action selection;
- three-step sampled SARSA target construction with `gamma = 0.99`, early-terminal shortening, and an externally supplied sampled-action bootstrap distribution;
- canonical Munchausen reward shaping using `r + alpha * tau * log(pi(a|s))`, `alpha = 1/16`, `tau = 1/8`;
- the requested `1/2^16` L2 gradient coefficient.

There is **no LSTM** and **no epsilon-greedy branch** in the canonical source. The actor's NoisyNet parameters and noise state are separate from the deterministic critic.

This is not yet a complete trainable agent. The following remain to be implemented and verified: specialized CHAD/Iterate-CHAD pullbacks and their complexity theorem; quantile-Huber loss and learned FQF-fraction gradients; ObGD parameter updates; the UTD=2 sequential training loop; and end-to-end training/runtime parity tests. The current source provides the network forward path, policy sampling, reward shaping, and SARSA target, rather than claiming those remaining pieces are complete.

## Fixed-width numeric contract

The widths are explicitly declared in Agda and mapped into Haskell by Agda2HS:

| Agda type | Haskell representation | Role |
| --- | --- | --- |
| `Int32` | `Data.Int.Int32` | Q12.20 parameters, activations, rewards, gradients, quantile values and dimensions |
| `Int64` | `Data.Int.Int64` | widened products, reductions, division numerators and intermediate accumulation |
| `Word32` | `Data.Word.Word32` | PCG output word and bit operations |
| `Word64` | `Data.Word.Word64` | PCG state, actor seed and deterministic sampling |
| `Int8` | `Data.Int.Int8` | optional packed Q1.6 inference weights |

Q12.20 uses scale `2^20 = 1,048,576`. The signed Int32 range represents values from -2048 through approximately 2047.999999. Multiplication widens to Int64, rounds ties to even, and saturates on narrowing. Division returns an explicit zero-divisor result.

The type declarations are in `FullCoupled/CanonicalLearnerMonolith.agda`, not merely hidden inside the foreign Haskell block. The corresponding `COMPILE AGDA2HS ... existing` declarations connect Agda's opaque types to their Haskell representations.

These width choices are the learner's explicit fixed-point design. Viktor Csimma's Agda2HS work establishes extraction and FFI techniques; it does **not** prescribe Int32/Int64/Word32/Word64 as a universal numerical policy. Acorn's exact-real implementation uses arbitrary-precision Haskell `Integer` in its dyadic/rational layer. This repository deliberately chooses bounded Q12.20 arithmetic for its runtime network.

No floating-point types, literals, conversions, or floating-point arithmetic are used by the learner kernels. `Haskell.Prelude` remains the standard Agda2HS programming surface; unused Prelude facilities are not part of the learner's extracted runtime operations.

## Composed executable network

`NetworkParams`, `NetworkState`, and `NetworkStep` assemble the individual components into one causal recurrent inference step:

1. The state-independent-candidate GRU consumes the observation and prior hidden state.
2. The observation and new hidden state are concatenated.
3. The actor-only factorized NoisyNet head computes policy logits, Quantmoid4-normalized probabilities, and a discrete Gumbel-Max sampled action at temperature 1/8.
4. The deterministic FQF critic evaluates that sampled action and returns its quantile distribution and mean value.
5. The actor noise persistence counter advances; critic and recurrent computations never receive actor noise.

`networkSarsa3Target` uses the distribution associated with the behavior action sampled at the third step. `networkMunchausenReward` applies the signed log-policy shaping term to the selected action. There is no epsilon-greedy selector and no LSTM implementation.

This provides a composed **forward network and target-construction path**. It does not yet provide a complete training loop: quantile-Huber gradients, learned FQF fraction gradients, CHAD pullbacks, ObGD updates, UTD=2 sequencing, and end-to-end training verification remain outstanding.

## Recurrent cell

For input vector (x_t) and previous hidden state (h_{t-1}):

```text
g_t = shifted_rescaled_softsign(W_g x_t + b_g)
c_t = W_c x_t + b_c
m_t = g_t ⊙ h_(t-1) + (1 - g_t) ⊙ c_t
h_t = softsign(MADLayerNorm(m_t))
```

The candidate projection depends only on the current input. It has no recurrent-state term and no candidate activation. The gate is in the convex interval by construction of the shifted/rescaled softsign. The integer forward implementation is in the foreign block; the smooth dyadic shadow and CHAD VJP still need to be added before claiming differentiable training correctness.

## Critic and SARSA

The FQF critic has separate fraction and quantile-value projections. The intended training configuration is 16 learned fractions and 16 quantile values per action. Fractions are normalized with the integer Quantmoid4-based policy-normalization kernel and converted into cumulative midpoint locations.

Three-step target:

```text
G_t = r_t + gamma r_(t+1) + gamma^2 r_(t+2)
      + gamma^3 Z(s_(t+3), a_(t+3))
```

The bootstrap distribution is evaluated at the action actually sampled by the actor at step three. Earlier termination shortens the return. No action maximum appears in the target. This avoids the classic max-selection mechanism behind Q-learning's maximization bias, but does not guarantee an unbiased estimate.

The composed `networkStep` runs the GRU, actor and deterministic critic in one causal transition. The bootstrap distribution is taken from the behavior action sampled by that step. Quantile-Huber loss, its gradients, and the complete optimizer-driven update remain outstanding.

## Actor, noise and Munchausen shaping

Factorized noise applies only to actor weights and biases. The critic parameters are deterministic. Actor noise is held for a sampled persistence duration from a discrete lognormal approximation table; PRNG and sampling state use Word32/Word64. The selected action uses integer Gumbel-Max perturbation at temperature `1/8`; policy probabilities use the Quantmoid4-normalized integer kernel.

Munchausen shaping is the canonical signed log-policy term:

```text
rM = r + (1/16)(1/8) log(pi(a|s))
```

The log-probability is a bounded integer lookup approximation. Probabilities below the table's minimum knot are clamped, so an explicit approximation-error bound is required before training results can be interpreted quantitatively.

## Agda2HS import surface

The canonical file explicitly imports:

```agda
open import Agda.Primitive using (Level; _⊔_)
open import Haskell.Prelude public
open import Agda.Builtin.Erased.Funext public
open import Agda.Builtin.Erased.Propext public
open import Agda.Builtin.Erased.Quotient public
open import Agda.Builtin.Equality.Rewrite public
```

`Haskell.Prelude` follows the normal Agda2HS base-library convention used in Csimma's examples. The Agda 2.9 erased-logic modules and builtin equality rewriting are project additions. The learner has no GUI, IORef, pointer, StablePtr, MVar, CFuture, C string, or platform-specific runtime interface.

The source's proof packaging and vector-length indices are erased. Agda's builtin `Nat` is obtained from the Prelude and used only as an erased vector index; it is not the learner's numeric representation.

## Build and verification

Nix pins the Agda 2.9-compatible Agda2HS toolchain and its matching base library. The `agda-ci` shell provisions LuaRocks, Lanes and Lua Fun. The Fennel runner launches the two Agda typechecks concurrently in isolated temporary source trees with local interface files.

```sh
nix develop --quiet .#agda-ci -c fennel .ci/fennel/parallel-agda.fnl
nix develop --quiet .#agda-ci -c fennel .ci/fennel/ci.fnl All
```

A successful Agda typecheck and extraction do not validate foreign Haskell arithmetic by themselves. Required checks include integer boundary/rounding tests, Quantmoid4 reference vectors, GRU range and state-independence tests, actor-noise isolation, SARSA terminal alignment, FQF fraction normalization, Munchausen approximation error, CHAD primal/VJP simulation, ObGD bounds, and extracted-Haskell parity.

## Repository layout

```text
.
├── .ci/
│   ├── agda/
│   └── fennel/
├── .github/workflows/github-pages.yml
├── FullCoupled/
│   ├── CanonicalLearnerMonolith.agda
│   └── TheoremsMonolith.agda
├── flake.nix
├── README.md
├── index.html
└── site.css
```

## References

- Viktor Csimma, *Adapting the MVVM pattern to C++ frontends and Agda-based backends* (2026): https://arxiv.org/abs/2603.24199
- Viktor Csimma, *Acorn: an agda2hs-compatible representation of exact real arithmetic* (2023): https://csimmaviktor.web.elte.hu/acorn.pdf
- Agda2HS documentation: https://agda.github.io/agda2hs/
- Csimma's Agdalache implementation: https://github.com/viktorcsimma/agdalache
- Csimma's Acorn implementation: https://github.com/viktorcsimma/acorn
- Stockfish NNUE Quantmoid4 reference: https://github.com/official-stockfish/nnue-pytorch/blob/master/docs/nnue.md
