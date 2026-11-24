# ADR 0001: QR64 Double Online SARSA(0) with Dueling NoisyNets

- Status: proposed architecture; not yet present in the Agda learner
- Scope: recurrent distributional critic and online update semantics
- Supersedes: scalar actor-critic / categorical-policy / scalar-Q design

## Decision

Replace the actor-critic with two independently parameterized, fully online
dueling distributional critics. Each critic predicts 64 return quantiles per
action and uses factorized NoisyNet parameters. There is no actor, replay
buffer, frozen target network, multi-step target, or repeated update per
transition.

The update invariant is exactly one critic update for each environment
transition: UTD = 1. A transition is consumed once, then discarded. There is
no replay or re-sampling of an old transition.

The two critics are named A and B. They remain live and trainable throughout.
At an episode boundary, the active critic flips. Within an episode, the active
critic selects the next action and receives the update; the other live critic
evaluates that same next action. Holding the active side fixed until terminal
is intentional: it makes the selected SARSA action at the next observation
the action consumed by the next transition, instead of changing behavior
policy between adjacent transitions.

For an episode whose active critic is A:

1. Select current action from A's noisy dueling distribution.
2. The environment supplies one transition (s, a, r, s', terminal).
3. For a nonterminal transition, select a' by maximizing A's mean quantile
   value at s'.
4. Evaluate that exact a' with B. B performs no second argmax.
5. Update A once with the 64-quantile QR-Huber loss.
6. Return a' as the next behavior action. At terminal, bootstrap is zero and
   the active side flips for the next episode.

The B-active case is symmetric. Both critics receive updates on alternating
episodes; every transition still causes one and only one parameter update.

## Distributional dueling head

For quantile index i in 0..63, use tau_i = (i + 1/2) / 64.

Each critic emits a value quantile V(s, tau_i) and an advantage quantile
A(s, a, tau_i) for every action. Combine them as:

    Z(s,a,tau_i) = V(s,tau_i) + A(s,a,tau_i) - mean_b A(s,b,tau_i)

The advantage-centering mean is over actions at a fixed quantile index.
It is not a mean over quantile indices.

Action selection uses the expected value of the predicted return
distribution:

    a* = argmax_a mean_i Z(s,a,tau_i)

## Double-online SARSA(0) target

Let C be the active critic and Cbar the other live critic. The next action is
selected by C and evaluated by Cbar, with one shared action identity:

    a' = argmax_a mean_i Z_C(s', a, tau_i)
    y_j = r                                      terminal
    y_j = r + gamma * Z_Cbar(s', a', tau_j)       otherwise

The target consists of exactly one reward and one next-state distribution.
There is no n-step accumulation. The evaluator receives the selected action;
it does not select a separate action. No frozen or delayed copy of either
critic is introduced.

This is a Double-Q SARSA(0) design. The term “True Online SARSA(0)” is used
with a precise caveat: at lambda = 0 the Dutch eligibility-trace correction
vanishes, so the temporal target reduces to ordinary one-step SARSA(0).
Any recurrent reverse scan used to differentiate a finite neural sequence is
a gradient-through-time mechanism, not a multi-step return target.

## QR64 regression

For current quantile z_i and target quantile y_j, define delta_ij = y_j - z_i.
The pairwise quantile-Huber loss is:

    rho_tau^kappa(delta) = |tau - 1[delta < 0]| * H_kappa(delta)

The mean loss is over all 64 x 64 pairs. The Huber derivative is bounded by
kappa; this is the derivative of the chosen loss, not global gradient
clipping. The implementation must preserve quantile-index weighting and
the full pairwise reduction. Tests must cover positive, negative, zero, and
Huber-boundary deltas.

Terminal targets contain 64 copies of reward, with no bootstrap term.

## NoisyNet parameters

Noise belongs to critic value and advantage layers. Every noisy scalar
parameter has a learned mean and learned scale. The forward pass receives an
explicit noise sample; it does not draw randomness internally. For a
factorized layer, transformed input and output factors form weight noise,
and the output factor forms bias noise. A host-side sampler supplies the
Gaussian factors. Passing the sample explicitly keeps the Agda transition
pure and makes tests deterministic.

No actor noise or actor parameter remains. Tests must establish that setting
all noise scales to zero recovers the deterministic mean network and that
nonzero scales alter critic values while leaving action/head dimensions
unchanged.

## Recurrent feature and derivative contract

Remove softsign from every path participating in the recurrent VJP. Use the
shifted, rescaled Quantmoid4 tanh approximation:

    q4tanh(x) = 2 * Quantmoid4(x / 2) / 126 - 1

This centering maps the documented Quantmoid4 output range [0, 126] onto
[-1, 1]; input scaling gives the tanh relation tanh(x) = 2 sigmoid(2x) - 1.

The implementation must name two distinct objects:

- the quantized Quantmoid4 forward approximation used by the cell;
- its explicitly documented smooth-shadow derivative used by iterative CHAD.

The smooth-shadow derivative is a training surrogate. It must not be described
as the derivative of integer quantization. Test forward symmetry, bounded
range, zero point, saturation behavior, and derivative behavior on each
piecewise region. Keep the recurrent reverse scan newest-to-oldest, with the
future cotangent threaded once per cached frame.

## Optimizer contract

Remove the current max-gradient normalization state and fixed implicit
weight shrink. Do not substitute gradient clipping.

For data gradient g and parameter w, use a separately named L2 gradient term:

    g_regularized = g + l2_gradient_decay * w
    w_next = w - learning_rate * g_regularized

The regularization coefficient is independent of learning rate. This is
coupled L2 gradient regularization, not AdamW-style decoupled weight decay.
No hidden gradient norm clamp is permitted. Test the data-gradient-only case
when the coefficient is zero and the exact regularization direction when the
data gradient is zero.

## Agda model boundaries

The Agda state should make these distinctions explicit:

- ActiveCritic = A | B;
- two independent online critic parameter values;
- a non-empty action collection;
- exactly 64 quantile outputs per value and per action-advantage head;
- explicit NoisyNet noise input;
- an environment transition consumed once;
- terminal and nonterminal target cases;
- exactly one update result and the next behavior action.

The update API should accept current observation/action, reward, next
observation, terminal flag, active side, and explicit noise samples. It should
return the updated pair of live critics, next action when nonterminal, and
the next active side only at terminal. A replay API, target-network state,
actor state, n-step horizon, or update-count loop is outside the model.

## LuaFun / Fennel build boundary

Fennel, Teal, and YueScript all compile or load code for the Lua runtime;
LuaFun compatibility is determined by generated Lua version, module
resolution, and ABI. This project standardizes on Fennel.

Only basic, non-cloning iterator operations are allowed in repository Lua or
Fennel code: map, filter, foldl, range, totable, any, and simple traversal.
Do not use iterator cloning, repetition, cycle, partition, split/span,
iterator emptiness inspection, or S/S-prime contraction-style combinators.
Standard Lua string.gmatch generators are materialized into a table before
passing values into LuaFun, because they do not use LuaFun's
generator/parameter/state triple.

Fennel and LuaFun are Nix-pinned. Lua Lanes is installed into the project-local
LuaRocks tree. Lane workers own distinct Agda workspaces and launch separate
Agda subprocesses.

## Agda-linear connection

Trebor Huang's agda-linear is a focused linear type-theory implementation
with explicit context splitting and occurrence accounting. It is useful as a
design reference for single-consumption transition tokens, one-shot noise
samples, and disjoint ownership of A/B update permissions. It is not imported
as a numerical or CHAD dependency: its type theory and foundation are
different from this Agda2HS learner module.

The concrete learner should encode one-update-per-transition structurally
where practical. A transition token must not be duplicated or retained for a
later replay update.

## Required verification before claiming completion

1. Agda type-checks new critic records, QR64 operations, target, and update.
2. Agda2HS extraction and generated Haskell typecheck pass.
3. Small tests cover terminal/no-bootstrap and both A/B select-evaluate cases.
4. A test confirms evaluator receives selected action without a second argmax.
5. QR64 pairwise loss tests cover all sign/Huber branches and exact atom count.
6. NoisyNet zero-noise parity and noise-shape tests pass.
7. Quantmoid4 forward/smooth-shadow derivative tests pass.
8. L2-gradient-decay direction tests pass and no gradient-clipping path exists.
9. Static audit finds no actor, categorical policy, scalar-Q target,
   softsign derivative, replay state, target-network state, multi-step target,
   or forbidden LuaFun iterator.
10. CI verifies Fennel parsing, Pages generation, Agda, Agda2HS, and GHC.

Until these checks pass, this ADR is a design decision, not evidence that the
learner implementation already has this architecture.
