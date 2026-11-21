# Deep Watkins Monoid RNN

An Agda-first, Agda2HS-extracted recurrent actor-critic learner. The single canonical learner source is `FullCoupled/CanonicalLearnerMonolith.agda`; fixed-width vector kernels live behind its narrow Haskell FFI boundary.

## Network architecture

The canonical module contains an actual composed recurrent neural network, not just disconnected layer sketches:

```text
observation + previous hidden
          │
          ▼
state-independent-candidate affine GRU
          │
          ▼
 MAD-LayerNorm → softsign
          │
          ├── concatenate observation + new hidden
          │
          ├──────────────────────────────────┐
          ▼                                  ▼
actor-only factorized NoisyNet       deterministic FQF critic
          │                                  │
Quantmoid4 policy probabilities       16 quantiles, learned fractions
          │                                  │
quantized-log Gumbel-Max action ─────► sampled-action evaluation
          │
persistent quantized noise duration
```

The candidate branch is affine in the current observation only. It has no previous-hidden-state term and no candidate activation. The gate is a shifted/rescaled softsign; the hidden-state update is a convex mix followed by MAD-LayerNorm and softsign.

The critic is deterministic. Factorized NoisyNet parameters and noise state belong exclusively to the actor. The selected action is sampled by Gumbel-Max using the same Quantmoid4-normalized policy probabilities returned in `NetworkStep`. The Gumbel score uses a range-reduced integer logarithm of those probabilities; the reward-shaping path separately clamps probabilities below `2^-16`. This keeps sampling and reported policy probability aligned up to Q20 and quantized-Gumbel error.

There is **no LSTM** and **no epsilon-greedy selector** in the canonical learner source. The CI source audit rejects either strategy name in this file.

## Fixed-width types: explicit Agda declarations

Viktor Csimma's Agda2HS work does not mandate these widths as a universal numerical recommendation. Its relevant point is that Haskell machine integers are not native Agda builtin types; an Agda2HS project must establish the representation bridge. This repository now declares the machine types in Agda and maps them explicitly:

| Agda type | Extracted Haskell type | Project role |
| --- | --- | --- |
| `Int32` | `Data.Int.Int32` | Q12.20 parameters, activations, rewards, quantile values and gradients |
| `Int64` | `Data.Int.Int64` | widened products, reductions and CHAD cotangent accumulation |
| `Word32` | `Data.Word.Word32` | PRNG output word and bit operations |
| `Word64` | `Data.Word.Word64` | PRNG state and deterministic sampling seed |
| `Int8` | `Data.Int.Int8` | optional packed Q1.6 inference weights; project-specific, not a Csimma requirement |

The corresponding Agda declarations are opaque postulates with `COMPILE AGDA2HS ... existing` mappings. Q12.20 uses scale `2^20 = 1,048,576`. Int32 arithmetic widens to Int64 for products and reductions, rounds ties to even, then saturates on narrowing. Division-by-zero has an explicit result constructor. The vector-length index is erased; Agda's builtin `Nat` is a type-level length witness, not the runtime numeric representation.

No floating-point values or floating-point operations occur in the learner's fixed-point kernels. The optional Int8 path is a storage/inference choice; master parameters and training directions remain Int32.

References: [Csimma, “Reasonable Agda Is Correct Haskell” (Haskell '22)](https://csimmaviktor.web.elte.hu/ReasonableAgdaIsCorrectHaskell.pdf), [Agda2HS documentation](https://agda.github.io/agda2hs/).

## Integrated policy and target construction

The canonical network exports these composed operations:

- `networkStep`: causal GRU transition, actor probabilities, Gumbel-Max sampled action, deterministic selected-action FQF distribution, value and next state.
- `networkStepForAction`: same causal transition and critic evaluation for a supplied behavior action; useful when the collector supplies the action.
- `networkMunchausenReward`: signed log-policy shaping for the action actually taken.
- `networkSarsa3DistributionalTarget`: three-step sampled SARSA target; preserves the bootstrap FQF widths while shifting/scaling its quantile values.
- `networkMunchausenSarsa3Target`: composes Munchausen shaping for all three behavior rewards with the sampled distributional SARSA target.
- `networkTrainSampleFromTarget`: packages target widths and target quantiles for the learner.

The three-step backup uses the behavior action at the bootstrap state, never an action maximum. Terminal flags shorten the return at the first terminal transition. Munchausen shaping uses `r + alpha * tau * log(pi(a|s))`, with `alpha = 1/16` and `tau = 1/8`. The logarithm uses a range-reduced fixed-point series; the reward-shaping path clamps probabilities below `2^-16`. A numerical error bound and cross-check against a high-precision reference still need to be added.

## FQF and quantile-Huber learner

The critic fixes the fraction/value count at 16. The fraction head is normalized into positive widths, cumulative widths give quantile midpoints, and the value head gives action-specific quantile estimates. The pairwise quantile-Huber loss and its descent direction are implemented in the integer kernel.

The FQF fraction-proposal direction follows the structure of Proposition 1 in the FQF paper: each interior boundary uses the difference between twice the quantile value at the boundary and its neighboring midpoint quantile values. Since this project has discrete learned quantile samples rather than an exact inverse-CDF oracle, the boundary value is obtained by piecewise-linear interpolation between adjacent midpoint estimates. That is an explicit numerical surrogate, not an exact symbolic inverse-CDF gradient. [Fully Parameterized Quantile Function](https://proceedings.neurips.cc/paper_files/paper/2019/hash/f471223d1a1614b58a7dc45c9d01df19-Abstract.html).

## Iterative CHAD integration

The canonical learner now connects the network's GRU, actor and FQF pullbacks through one state-passing reverse scan:

- `linearRowsVJP`, `noisyLinearVJP`, `gruStepVJP`, `actorLogProbabilityVJP`, and `fqfActionVJP` provide local smooth-shadow pullbacks.
- `networkStepVJP` joins the policy, value/fraction and recurrent cotangents at the shared feature vector and returns the previous-hidden and observation directions.
- `networkParameterVector` and `networkWithParameterVector` define one canonical parameter order across all three components.
- `iterativeCHADForward` stores the finite primal trace; `iterativeCHADBackward` traverses that trace in reverse, passes the hidden-state cotangent between frames, and merges parameter directions.
- Parameter cotangents are lifted to Int64 vectors during the reverse scan and narrowed once after the complete unroll. This avoids the non-associativity introduced by saturating Int32 addition at every time step.

The Agda work-count model proves that an unroll of length `n` has exactly `n` forward-cell frames, `n` reverse-cell applications and `n` parameter-accumulator merges. With dense parameter dimension `P), those vector merges cost `O(nP)`; the saved primal trace is linear in horizon and per-step state/input/output storage. This is a bound for the explicit scan and dense vector representation here, not a theorem about every CHAD program.

The implementation is an iterative, state-passed CHAD-style scan for this learner. It is not a general source-to-source CHAD compiler, and the FFI kernels' smooth-shadow VJPs do not yet have a machine-checked derivative-correctness theorem. Integer rounding, saturation, table lookups, factorized noise samples and Gumbel-Max selection are discrete boundaries; pullbacks differentiate the declared smooth Q20 shadow while holding those sampled/discrete choices fixed.

Research context: [Unraveling the Iterative CHAD](https://arxiv.org/abs/2505.15002), [Efficient CHAD](https://arxiv.org/abs/2307.05738).

## ObGD and sequential UTD=2 updates

The learner includes:

- `qTraceAdvance`: decayed eligibility/update-direction trace.
- `l2Gradient`: an update direction with coefficient `16 / 2^20 = 1/2^16), pointing toward zero.
- `qObgdEffectiveStep` and `qObgdUpdate`: a conservative Q20 step bound based on the configured curvature factor, residual magnitude and L1 trace norm.
- `networkTrainSequenceVJP`: full finite-horizon reverse-mode pass over chronological training samples.
- `networkTrainSequenceUTD2`: two updates per sample with one-step truncated BPTT; recurrent and noise time advance once per environment sample.
- `networkTrainChunkUTD2`: two parameter updates per non-empty chronological chunk, using full-unroll CHAD/BPTT; recurrent/noise state advances once per chunk.

The ObGD step is applied to the combined policy/value/fraction update direction, with unit scalar residual because each component direction already contains its own actor advantage or quantile-Huber residual. This is a gradient-direction adaptation of the ObGD bound, not a proof that the paper's scalar-TD convergence theorem transfers unchanged to this mixed objective. The two UTD=2 entry points have different horizons as stated above; choose the full-unroll chunk operation when recurrent credit assignment across the chunk is required.

Training samples and target distributions are supplied by the caller. The module does not yet supply an environment, data loader, replay store, or behavior collector. It is therefore a connected learner/update core, not a turnkey RL application.

## Verification and trust boundary

CI typechecks the Agda modules, extracts the canonical module with Agda2HS, typechecks the generated Haskell module with GHC, audits for forbidden LSTM/epsilon-greedy paths and checks that the composed network/CHAD/UTD2 entry points exist. A green extraction/typecheck verifies the declared Agda and Haskell interfaces; it does not establish numerical parity or the mathematical correctness of every foreign kernel.

Still needed for a verified training claim:

- property tests for saturating arithmetic, ties-to-even rounding, fixed-point division and Quantmoid4 reference vectors;
- finite-difference/reference tests for GRU, MAD-LayerNorm, actor, quantile-value and FQF fraction pullbacks;
- actor-noise isolation, selected-action probability and Gumbel sampling distribution checks;
- terminal/bootstrap alignment and Munchausen lookup-error bounds;
- ObGD step-bound tests and extracted-Haskell runtime parity tests;
- an end-to-end chronological training run on a documented data set.

Run locally:

```sh
nix develop --quiet .#agda-ci -c fennel .ci/fennel/parallel-agda.fnl
nix develop --quiet .#agda-ci -c fennel .ci/fennel/ci.fnl All
```

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
