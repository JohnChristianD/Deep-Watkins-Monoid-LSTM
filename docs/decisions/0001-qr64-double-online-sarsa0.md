# ADR 0001: IQN32 Double Online SARSA(0) with Dueling NoisyNets

- Status: selected architecture; not yet implemented in the Agda learner
- Scope: recurrent distributional critics, one-step online action/value semantics, affine update ownership
- Supersedes: scalar actor-critic / categorical-policy / scalar-Q design and the earlier QR64 proposal

## Decision

Replace the actor-critic with two independently parameterized, live dueling
Implicit Quantile Network critics, A and B. There is no actor. Each critic
predicts a return quantile function for every action and uses factorized
NoisyNet parameters in its value and advantage layers.

Here, **IQN32** means 32 sampled current quantile fractions and 32 sampled
target quantile fractions per transition, with a 32-component cosine quantile
embedding. These are Monte Carlo samples of the implicit quantile function,
not 32 fixed output bins.

The learner is fully online: A and B are both current trainable parameter
sets; neither is a delayed or frozen target copy. At each transition, exactly
one critic receives one optimizer update. The active side remains fixed during
an episode and flips at a terminal boundary. The other live critic evaluates
the selected next action without selecting a second action. Thus UTD is 1,
and every environment transition is consumed once. There is no replay, no
re-sampling of old transitions, and no multi-step return.

This alternating-episode schedule preserves the on-policy SARSA action
identity across adjacent transitions. It is a design choice, not a claim that
the non-active critic is updated on every individual transition.

## Dueling IQN32 head

For quantile fraction \(\tau\in[0,1]\), critic \(C\), observation \(s\),
and action \(a\), each critic emits value and advantage quantile functions:

\[
Z_C(s,a,\tau)=V_C(s,\tau)+A_C(s,a,\tau)
-\frac{1}{|\mathcal A|}\sum_{b\in\mathcal A}A_C(s,b,\tau).
\]

Advantage centering is over actions at one fixed quantile fraction. It is not
an average over quantile samples.

For IQN32, sample \(\tau_i\) and \(\hat\tau_j\), for
\(i,j\in\{1,\ldots,32\}\), from the unit interval. The 32-dimensional
quantile embedding uses the standard cosine features
\(\cos(\pi k\tau)\), \(k=0,\ldots,31\), followed by a learned embedding
network. The host supplies the fractions explicitly; the pure Agda update
does not draw randomness internally.

Action selection uses the sample mean of the quantile values:

\[
a'=\arg\max_{a\in\mathcal A}
\frac{1}{32}\sum_{i=1}^{32}Z_C(s',a,\tau_i).
\]

## Double-online SARSA(0) target

Let \(C\) be active and \(\bar C\) the other live critic. For a
nonterminal transition, the active critic selects one next behavior action
and the other critic evaluates that exact action:

\[
a'=\arg\max_a\frac{1}{32}\sum_i Z_C(s',a,\tau_i),
\qquad
y_j=r+\gamma Z_{\bar C}(s',a',\hat\tau_j).
\]

For a terminal transition, \(y_j=r\) for every \(j\); there is no
bootstrap. The evaluator receives \(a'\) as input and has no argmax or
action-selection operation.

The selected \(a'\) is also the action consumed by the next environment
transition. Carry it in a one-use pending-decision value with the required
recurrent forward cache and explicit active-critic noise sample. Do not
re-sample the action or silently evaluate a different noisy network at the
same decision boundary.

The current critic quantiles are
\(z_i=Z_C(s,a,\tau_i)\). Use the complete 32-by-32 quantile-Huber
regression loss:

\[
\mathcal L=\frac{1}{32^2}\sum_{i=1}^{32}\sum_{j=1}^{32}
|\tau_i-\mathbf 1[y_j-z_i<0]|\,
H_\kappa(y_j-z_i).
\]

Target-side quantiles are stop-gradient values. Only the active critic is
updated on this transition.

At \(\lambda=0\), the Dutch-trace correction in True Online SARSA(\lambda)
collapses and the return target is ordinary one-step SARSA(0). Quantile
regression can be used for that one-step distributional target, but it does
not make the classic scalar True-Online correction non-vacuous. The precise
name for this learner is **Double distributional SARSA(0), with the
\(\lambda=0\) True-Online limit**. The recurrent reverse scan differentiates
the current network computation; it does not create an n-step return.

## NoisyNet contract

Noise belongs to the critic's value and advantage layers. Every noisy
parameter has a learned mean and scale. The forward computation accepts an
explicit factorized-noise sample; it performs no hidden random draw.

The active critic's selected action, noisy sample, and relevant recurrent
cache are bundled as one pending decision and consumed by the next transition.
The inactive critic receives its own explicit noise sample for evaluation,
but never re-selects the action. Tests must verify that zero noise scales
recover the deterministic mean network and that nonzero noise changes values
without changing action or quantile dimensions.

## Recurrent feature and Quantmoid4 derivative contract

Remove softsign from the recurrent cell and every iterative-CHAD derivative
path. Use the shifted/rescaled Quantmoid4 approximation for tanh-like bounded
features:

\[
q4\_tanh(x)=\frac{2\,Q4(x/2)}{126}-1,
\]

where \(Q4\) is Stockfish-style Quantmoid4, an integer piecewise-quadratic
approximation of \(\sigma(4x)\) with output range \([0,126]\). This scaling
maps the zero point to zero and the output interval to \([-1,1]\), while
approximating \(\tanh(x)\).

Keep two separately named definitions:
- the quantized Quantmoid4 forward function;
- a smooth-shadow derivative used by iterative CHAD.

For the smooth sigmoid shadow
\(p=\sigma(2x)\), the corresponding derivative of the transformed smooth
tanh shadow is \(4p(1-p)\). This is a training surrogate, not the derivative
of integer Quantmoid4 rounding. The implementation must state its branch
and saturation conventions and test each piecewise region.

**Do not replace the IQN cosine quantile embedding with q4_tanh.** Cosine
features are periodic and distinguish quantile frequencies; q4_tanh is
monotone and bounded. Substitution changes the quantile embedding semantics
and produces a different Q4-embedded implicit quantile model, not the selected
standard IQN32 design. Likewise, q4_tanh is not a semantics-preserving
replacement for logarithm or hyperbolic cosine over their domains. Use it
only where a tanh-like bounded activation is intended. Preserve any other
function whose domain, range, or algebraic role differs.

The recurrent reverse scan remains newest-to-oldest, threading the future
hidden cotangent exactly once per cached frame. Its surrogate derivative must
be explicitly separated from the integer forward map.

## Euclidean Q-projected IDBD

Replace the current max-gradient normalization and implicit fixed weight
shrink with per-parameter Incremental Delta-Bar-Delta (IDBD) state. For each
parameter \(w_i\), retain a log step-size \(\beta_i\) and IDBD sensitivity
trace \(h_i\). Set \(\alpha_i=\exp(\beta_i)\).

Let the data gradient of the 32-by-32 quantile-Huber objective be
\(g_i^{data}=\partial\mathcal L/\partial w_i\). Apply a separately named
L2 gradient term:

\[
g_i=g_i^{data}+\texttt{l2\_gradient\_decay}\,w_i.
\]

Use the diagonal IDBD sensitivity update

\[
w_i'=w_i-\alpha_i g_i,
\qquad
h_i'=h_i-\alpha_i(g_i+\widehat H_{ii}h_i),
\]

where \(\widehat H_{ii}\) is the explicitly documented diagonal curvature
estimate for the regularized objective. The meta-step is

\[
\beta'=\Pi_Q^E(\beta-\mu(g\odot h)).
\]

Here \(Q=[\beta_{min},\beta_{max}]^n\) is a declared closed convex
feasible box, \(\Pi_Q^E\) is Euclidean projection, and the box limits,
meta-rate \(\mu\), curvature estimate, and fixed-point exponential
approximation are explicit configuration. The diagonal curvature makes this
a diagonal IDBD approximation; do not present it as a full Hessian method.

\texttt{l2\_gradient\_decay} is distinct from the IDBD meta-rate and from
the rate projection. It enters the data gradient before the IDBD weight step.
There is no global gradient-norm clipping, max-gradient normalization, or
hidden fixed shrink term. The quantile-Huber loss's own bounded derivative is
part of the chosen objective, not global gradient clipping.

Tests must cover: zero L2 coefficient; zero data gradient with nonzero
regularization; projection at both \(\beta\) bounds; positive step sizes;
meta-trace sign and curvature branches; and fixed-point approximation error.

## Affine resource discipline in the Agda type layer

Trebor Huang's `agda-linear` gives a useful implementation reference:
contexts record occurrences, and context splitting combines disjoint
resources. Adapt that accounting idea in the learner's type layer for:
- one transition/update token;
- one pending next-action decision;
- explicit noise samples;
- the active-critic update permission.

The intended learner boundary is affine: resources may be consumed at most
once, so replay and accidental duplication are unrepresentable in the
transition language. Some terminal-only values may be discarded, so a strict
linear encoding needs an explicit weakening/affine modality at those points.
Do not describe ordinary Agda function types as affine by themselves; the
property must be enforced by the encoded syntax/context checker or an
appropriate linear type discipline.

Keep critic A and B parameter ownership disjoint. The active critic receives
the unique update permission; the other critic receives a read/evaluation
permission for the target calculation. A terminal branch consumes the
transition and clears the pending decision without producing a bootstrap
action.

Bend is a separate, relevant reference: the current `bendlang/bend`
documentation describes affine values. It is not Trebor Huang's
`agda-linear` project, and it is not a substitute for the Agda-side
transition/context proof. No Bend runtime dependency is introduced.

## LuaFun / Fennel boundary

Fennel is the selected source language and YueScript is removed from the
toolchain. Teal, Fennel, and YueScript can all interoperate with Lua libraries
when generated code targets the same Lua version and the module path/runtime
ABI matches. Fennel is a project standard, not a unique LuaFun compatibility
requirement. The current shell uses LuaJIT's Lua 5.1 compatibility target.

LuaFun iterator values use the generator/parameter/state triple. The allowed
project subset is restricted to single-pass basic transformations and
reductions already used by the build: `map`, `filter`, `foldl`,
`range`, `totable`, `any`, and straightforward one-pass traversal.
Materialize foreign iterator forms such as `string.gmatch` before adapting
them to LuaFun.

A static audit must reject iterator cloning, replay, repetition, branching,
partitioning, splitting, state inspection, and explicit contraction helpers,
including `duplicate`, `replicate`, `xrepeat`, `cycle`, `is_null`,
`split`, `split_at`, `span`, `partition`, `tabulate`, `zeros`,
`ones`, `rand`, and `rands`. Extend the audit when an alias or equivalent
operation appears. Do not claim LuaFun itself supplies a BCK combinator API:
its pinned `fun.lua` exports iterator functions, not a named B/C/K basis.
Any BCK-only helper layer would be a separate local abstraction, not an
upstream LuaFun feature.

The Fennel build scripts remain orchestration code. Their file I/O, logging,
and process launches are effects at the build boundary; using pure callbacks
inside `map` or `foldl` does not make the whole CI driver pure. Lua Lanes
workers own isolated Agda workspaces and each launches its own Agda process.

## Verification required before claiming implementation

1. Agda type-checks the paired critic parameters, dueling value/advantage
   heads, IQN32 quantile fractions, and one-step target.
2. Agda2HS extraction and generated Haskell type-check pass.
3. Both A-active and B-active paths select once and evaluate the same action.
4. Terminal targets contain reward only; no bootstrap or pending action remains.
5. A selected next action is consumed as the following transition's action.
6. Tests verify exactly one critic update per transition, UTD = 1, and no replay.
7. IQN32 tests cover fraction bounds, 32-by-32 quantile-Huber weighting,
   action-centering per quantile, and target stop-gradient.
8. NoisyNet zero-noise parity, explicit noise flow, and action-cache alignment
   pass.
9. Quantmoid4 forward symmetry, zero point, range, saturation, and every
   smooth-shadow derivative region pass; no softsign derivative remains.
10. IDBD tests cover Q projection, meta-trace/curvature behavior, L2 direction,
    and absence of gradient clipping or hidden max-gradient state.
11. Type-layer tests demonstrate affine single-consumption and disjoint A/B
    ownership.
12. Static Lua/Fennel audit rejects every prohibited iterator/helper.
13. CI verifies Fennel parsing, Pages, Agda, Agda2HS, and GHC on the current
    head.

Until these implementation and verification checks pass, this ADR is a
selected architecture, not evidence that the current learner has been
converted. Keep PR #335 Draft and do not merge.
