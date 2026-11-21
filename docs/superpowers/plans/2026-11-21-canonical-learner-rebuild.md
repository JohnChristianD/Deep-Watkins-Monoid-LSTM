# Canonical Integer Learner Rebuild Implementation Plan

> **For agentic workers:** Use a test-first implementation. Keep all runtime Agda learner code in `FullCoupled/CanonicalLearnerMonolith.agda`; use focused tests and audit documentation around it.

**Goal:** Replace the 43-line extraction stub and superseded floating-point LSTM on `main` with a verified Q12.20, integer-only, CHAD-differentiable GRU and three-step FQF-SARSA learner.

**Architecture:** One canonical Agda monolith owns learner semantics, fixed-point arithmetic, recurrent transition, distributional critic, actor, optimizer, and proof witnesses. A narrow Agda2HS FFI adapter exposes only required fixed-width integer and unboxed-vector primitives. Erased proof packaging stays in Agda; C/IO/pointer/concurrency adapters stay outside the pure learner unless a concrete runtime seam requires them.

**Tech Stack:** Agda, agda2hs, Haskell `Int32`/`Int64`, `Data.Vector.Unboxed`, repository Nix/Agda CI.

**Spec:** PR #335 description plus the confirmed conversation requirements; conflicts and precedence are recorded below.

## Global Constraints

- All runtime learner, recurrent, CHAD, optimizer, and policy code remains in `FullCoupled/CanonicalLearnerMonolith.agda`.
- No `Float`, `Double`, floating literals, floating imports, floating conversions, or floating intermediate values in Agda or extracted Haskell.
- Primary numeric representation is signed Q12.20 in `Int32`; use `Int64` only for proven widened intermediates.
- Narrowing is explicit and checked or saturating; rounding is specified and tested.
- No epsilon-greedy, max-Q bootstrap, dueling head, ensemble, target network, Adamax, or momentum.
- Factorized NoisyNet applies to actor policy head only; critic/value head remains deterministic.
- Learner uses three-step sampled on-policy SARSA, `gamma = 0.99`, `lambda = 0`, and sampled bootstrap action.
- Distributional critic uses 16 learned FQF fractions and 16 quantile values per action, with quantile-Huber loss.
- Optimizer is ObGD; its bound must be justified for the aggregate quantile-Huber gradient.
- Munchausen shaping uses the canonical signed term `rM = r + alpha * tau * log(pi(a|s))`, with dyadic fixed-point approximation; do not silently reverse the sign into an optimistic surprisal bonus.
- Sequential samples remain causal and ordered; no replay shuffling or decorrelation.
- Quantmoid4's rounded integer forward path is discrete; CHAD differentiates a separately declared C1 dyadic shadow and proves/records the quantization discrepancy.
- No floating transcendental substitutes: log, softmax, Gaussian/noise transforms, reciprocal, and inverse-square-root require explicit bounded integer kernels or tables.

## Conflict decisions

1. PR #335 currently specifies an *optimistic low-probability surprisal bonus*. The later user clarification asks for ordinary Quantmoid4Max-Munchausen. Implement canonical Munchausen sign; keep the optimistic sign out unless separately requested.
2. Earlier PR text says no replay buffer, while the conversation requires causal sequential replay. Preserve contiguous chronological three-step windows; never shuffle or decorrelate them. Avoid inventing a random replay sampler.
3. Butterfly/Haar was previously requested as a decorrelator, then replay decorrelation was explicitly rejected. Exclude replay decorrelation. Retain a Butterfly/Haar transform only if source-level evidence establishes it as a deterministic observation transform with a tested inverse/range contract; otherwise remove it.
4. The current branch is a 43-line import/FFI stub, while `main` contains a 548-line floating-point-era implementation. Neither is a valid completed target. Do not copy the old LSTM forward unchanged.

## Review Focus

- Q12.20 extrema, negative rounding ties, zero divisors, and overflow in widened products.
- Quantmoid4 knots, saturation limits, and agreement between integer primal and dyadic shadow.
- Three-step SARSA with terminal at steps one/two/three, truncation, and bootstrap action alignment.
- FQF widths at zero/near-zero, strict fraction ordering, normalization, and quantile crossing.
- Actor noise resampling interval, deterministic critic isolation, and canonical Munchausen sign under low/high policy probability.

---

### Task 1: Restore a coherent canonical source and lock the import surface

**Files:**
- Modify: `FullCoupled/CanonicalLearnerMonolith.agda`
- Reference: `.ci/agda/global-options.txt`, `.ci/agda/agda2hs.yaml`
- Audit: `docs/agda2hs/csimma-import-audit.md`

**Interfaces:**
- Pure learner imports only selected Agda2HS primitives actually used.
- Haskell FFI declarations expose fixed-width integer and vector operations only.
- No C pointer, stable pointer, IORef, MVar, CFuture, or GHC concurrency imports.

- [ ] Write import-surface checks that reject floating names/types and forbidden adapter imports.
- [ ] Run checks against current branch and confirm they fail on `Haskell.Prelude`'s documented Double re-export.
- [ ] Replace broad Prelude re-export with the smallest supported selective imports, after confirming names against the pinned Agda2HS library.
- [ ] Define `Int32`, `Int64`, and vector FFI postulates with explicit COMPILE mappings; keep all foreign code in the canonical file's FFI block.
- [ ] Typecheck and extract the same canonical module.

### Task 2: Integer arithmetic kernel

**Files:**
- Modify: `FullCoupled/CanonicalLearnerMonolith.agda`
- Test: existing Agda CI plus focused integer-kernel checks in the repository's established test lane.

**Interfaces:**
- `Q20`: semantic fixed-point value backed by `Int32`.
- `wideMulQ20`, `divQ20`, `recipSqrtQ20`, `roundShiftEven`, `narrowQ20`: total, documented arithmetic operations.

- [ ] Add failing vectors for extrema, tie rounding, sign symmetry, overflow, zero denominator, and reciprocal-square-root bounds.
- [ ] Implement widened multiplication and explicit round-to-nearest-even.
- [ ] Implement normalized dyadic reciprocal table plus Newton refinement; retain exact integer division as reference/fallback.
- [ ] Implement integer reciprocal-square-root seed and Newton refinement.
- [ ] Run arithmetic checks and Agda typecheck.

### Task 3: Quantmoid4 and CHAD shadow

**Files:**
- Modify: `FullCoupled/CanonicalLearnerMonolith.agda`

**Interfaces:**
- `quantmoid4Q20 : Q20 -> Q20`
- `quantmoid4Shadow : Dyadic -> Dyadic`
- `quantmoid4ShadowDerivative : Dyadic -> Dyadic`

- [ ] Add failing knot, saturation, monotonicity, and shadow-derivative tests.
- [ ] Implement the integer piecewise-quadratic forward kernel.
- [ ] Implement a separate C1 dyadic shadow and derivative; document the exact knot convention.
- [ ] Prove or bound integer-forward versus shadow discrepancy and check CHAD VJP against finite differences of the shadow.

### Task 4: State-independent-candidate GRU

**Files:**
- Modify: `FullCoupled/CanonicalLearnerMonolith.agda`

**Interfaces:**
- `gruStep : GRUParams -> Hidden -> Features -> Hidden`
- Candidate projection is affine in current features and has no recurrent-state term.
- Gate is shifted/rescaled softsign in `[0,1]`; output applies the requested outer softsign.

- [ ] Add failing state-independence, gate-range, convex-mix, and boundary-derivative tests.
- [ ] Implement the candidate and gate with integer primal plus declared dyadic CHAD shadow.
- [ ] Prove the candidate is independent of prior hidden state and prove the gate range.
- [ ] Check primal/VJP simulation and fixed-point overflow bounds.

### Task 5: Three-step FQF-SARSA learner

**Files:**
- Modify: `FullCoupled/CanonicalLearnerMonolith.agda`

**Interfaces:**
- `sarsa3Target`: chronological rewards, terminal/truncation flags, and sampled third-step action determine target.
- `fqfFractions`: 16 positive widths normalized into 16 strictly increasing dyadic intervals.
- `quantileHuberLoss`: 16 quantile values/fractions and target distribution.

- [ ] Add failing tests for early terminal, final terminal, truncation, and correct sampled-action bootstrap.
- [ ] Implement `gamma = 0.99`, `lambda = 0`, and fixed three-step return without max-Q.
- [ ] Implement 16 learned FQF widths and boundaries; prove positivity, strict monotonicity, and unit sum within declared rounding tolerance.
- [ ] Implement quantile-Huber loss and dyadic-shadow gradient checks.
- [ ] Preserve contiguous chronological sample windows; no shuffling or replay decorrelation.

### Task 6: Actor, Munchausen shaping, and ObGD

**Files:**
- Modify: `FullCoupled/CanonicalLearnerMonolith.agda`

**Interfaces:**
- Actor policy uses factorized quantized noise and integer Q4-softmax at `tau = 1/8`.
- Critic/value head remains deterministic.
- Munchausen reward uses `r + alpha*tau*log(pi(a|s))`; `alpha = 1/16` unless the existing source defines another explicitly approved value.
- ObGD consumes aggregate quantile-Huber gradient without momentum.

- [ ] Add tests proving noise changes actor logits only and critic outputs are invariant to actor noise.
- [ ] Implement factorized noise with integer-only quantized-normal samples; sample factors once per action-selection interval.
- [ ] Implement integer softmax/log-probability lookup or bounded dyadic approximation.
- [ ] Add sign tests: low-probability actions receive a more negative canonical Munchausen term, not a positive optimistic bonus.
- [ ] Implement ObGD and prove its effective-step bound under the actual vector-gradient assumptions.

### Task 7: Whole-module proofs, extraction, and blast-radius review

**Files:**
- Modify: `FullCoupled/CanonicalLearnerMonolith.agda`
- Verify: `.ci/fennel/ci.fnl`, `.github/workflows/github-pages.yml`

- [ ] Typecheck canonical monolith.
- [ ] Extract canonical monolith with pinned `agda2hs`.
- [ ] Inspect extracted Haskell for floating types, conversions, and literals.
- [ ] Run full repository CI, including theorem, RUSS, and Pages lanes.
- [ ] Inspect the actual diff and PR checks; do not infer success from a successful isolated typecheck.
- [ ] Keep PR draft until every required check passes and all trust assumptions are documented.
