# Pure formal stack: target architecture and migration gates

## Goal

Make the executable search path small, deterministic, and auditable. Keep each tool inside its actual proof boundary. “Pure” means the deployable graph/search runtime depends only on the Agda2HS-supported subset and its pinned extraction/runtime dependencies. It does **not** mean an auxiliary prover result silently becomes an Agda proof.

## Component contract

### Agda2HS — executable reference implementation

- Keep executable graph/search definitions in `FullCoupled/Agda2HsSemanticSearch.agda` and e-graph behavior in `FullCoupled/Agda2HsTheoremGraphEGraph.agda`.
- Restrict extracted modules to the supported common Agda/Haskell subset, using `Haskell.Prelude` and the pinned `agda2hs-base`.
- Check Agda source before extraction. Compile generated Haskell with pinned GHC and `-dcore-lint`; execute deterministic fixtures and compare their outputs.
- Keep reflection, unsupported Agda features, and imported proof libraries outside the extracted runtime closure.
- Treat extracted Haskell as executable code whose behavior must be checked against the Agda source. Extraction alone is not a theorem of semantic preservation.

### Acorn — independent auxiliary proof checker

- Run Acorn as a separate lane for small, explicit propositions about finite graph fixtures or generated certificates.
- Record Acorn version, source proposition, assumptions, input artifact hash, and output.
- Acorn uses classical reasoning and choice. An Acorn result is not automatically a constructive Agda proof, a Curry–Howard proof term, or evidence accepted by the Agda kernel.
- Bridge a result only by exporting a certificate into a format that an Agda checker validates, or by proving the corresponding proposition independently in Agda. Until that bridge exists, label Acorn output “auxiliary cross-check,” never “Agda theorem proved.”

### XDS-Agda — isolated semantics research

- Keep Scott–Strachey/domain-theoretic experiments in a separate directory and separate CI lane.
- Pin its exact upstream revision and Agda/library versions before running it in CI.
- Inventory all postulates and axioms used by the selected modules. Any theorem depending on an unimplemented domain constructor, operation, or equivalence remains conditional on that postulate.
- XDS-Agda does not implement graph search and is not in the executable Agda2HS closure. It may inform a future semantics proof after the assumptions and interfaces are explicit.

### Mini-Vehicle / Vehicle — neural-network specification boundary

- Use Mini-Vehicle or Vehicle for high-level neural-network properties, such as the policy monotonicity and boundary-agreement properties in `Vehicle/CanonicalLearnerPolicy.vcl` and `Vehicle/CanonicalLearnerPolicyCorrespondence.vcl`.
- Pin the exact compiler, solver, and verification-cache inputs. A property with no verified cache or concrete network correspondence is not a proved property of the deployable model.
- Exported properties that are represented as postulates remain assumptions until checked by a trusted proof path. Keep those assumptions in the manifest.
- Do not move graph search or proof discovery into Vehicle; its role is to specify and check the neural-network boundary.

## Trust boundaries

| Lane | Accepted output | Not accepted as |
|---|---|---|
| Agda kernel | Checked theorem under recorded options and assumptions | Proof of an unrelated extracted program |
| Agda2HS + GHC | Executable artifact passing source, compile, and regression checks | Automatic proof that extraction preserves all source semantics |
| Acorn | Classical auxiliary result or independently checked certificate | Constructive Agda proof without a validated bridge |
| XDS-Agda | Conditional domain-semantics result with assumptions recorded | Assumption-free theorem when selected modules contain postulates |
| Mini-Vehicle / Vehicle | Verified network property for exact declared model/input/cache | Guarantee about an unrelated runtime model or missing cache |

Keep a machine-readable manifest with tool revisions, compiler versions, inputs, assumptions, checked propositions, artifacts, and regression outcomes. “No plugins” or a successful compiler exit is not a soundness claim.

## Current migration state (2026-10-13)

The active `flake.nix` no longer includes TypeTopology, Rio, or Mirth as build/runtime dependencies. Fennel runs through Nix-provided LuaJIT; Luafun is pinned and packaged with `buildLuaPackage`; Streamly packages are requested from the pinned Nixpkgs Haskell package set. CI checks the Agda2HS runtime closure and treats the legacy theorem files separately.

**Full source-level TypeTopology retirement is not complete.** `FullCoupled/TheoremsMonolith.agda` and `FullCoupled/LearnerLogicalSpec.agda` still import TypeTopology's integer, natural, rational, MLTT, univalence, ordinal, and searchable-type APIs. Their imports cannot safely be deleted without porting the used interfaces and proving the dependent lemmas, or deliberately removing those theorem surfaces. The current graph-search executable does not import either legacy file. Do not treat removal from `flake.nix` as proof that all historical Agda source is independent of TypeTopology.

Global executable Agda/Agda2HS flags are stored one-per-line in `.ci/agda/global-options.txt`; both Nix wrappers load that same file. Module-specific pragmas, such as `{-# OPTIONS --safe #-}` for the domain starter, remain source-local.

## Migration gates

1. **Lock down graph semantics.** Check linear-chain order, independent siblings, unique path identifiers, missing dependencies, cycle termination policy, score ordering, and finite fuel bounds. Generate the graph fixture deterministically; do not infer proof validity from a dependency edge.
2. **Separate runtime graph input.** Export a stable, versioned graph snapshot or simple edge manifest. Make the Agda2HS search app consume that artifact. Keep Agda dependency-graph generation and theorem-kernel checking in their own proof lane. Validate artifact schema, source revision, and hash.
3. **Retire TypeTopology in slices.** Inventory each imported symbol and dependent theorem. Port only the required interfaces into owned, auditable modules (or a deliberately chosen pinned library), then prove replacement lemmas. Remove `typetopology` from `flake.nix` only when no source or command references remain and all kernel lanes pass without its include path.
4. **Add sidecars reproducibly.** Add Acorn, XDS-Agda, and Mini-Vehicle/Vehicle lanes only after their toolchains are pinned and smoke-tested. Do not add an unpinned network installer or a speculative Nix package merely to make a flake look complete.
5. **Require closure proof.** CI must build from a clean checkout and verify the search fixtures, Agda kernel gates, Haskell extraction/GHC checks, sidecar assumptions, and generated manifests. Report each lane as pass, fail, unavailable, or blocked. Do not collapse them into one green Boolean.

The target is a small executable core plus explicitly separated proof sidecars. Full TypeTopology retirement is a gated migration, not a dependency deletion that leaves theorem imports unresolved.


## Agda command policy

The canonical global CLI flags are one-per-line in `.ci/agda/global-options.txt`. The Nix wrappers pass those flags to both `agda` and `agda2hs`. Use CLI spellings such as `--verbose=1`; short `-v=1` is source-pragma syntax and must not be passed through the wrapper. Keep flags with semantic or safety scope local to an individual file or CI lane. In particular, `--guardedness`, `--cumulativity`, `--rewriting`, and `--flat-split` stay file-local because passing them globally can make Agda's `--safe` imports reject their own option pragmas.

## Scott–Strachey and search semantics

Scott–Strachey lifted-natural semantics live in nested `ScottStracheyDomains` inside `FullCoupled/TheoremsMonolith.agda`; the standalone Scott file is removed. CI extracts that nested module into a temporary file and kernel-checks it without adding `--safe`. It distinguishes `bottom` from defined numeric zero and proves strict-addition examples. Strict lifted operations do not generally form a ring or semiring over the entire lifted carrier.

The canonical learner now defines a sized `LearnerStream` whose finite observation at index `n` is proved equal to `iterateCanonical n`, so index zero is the initial state and each tail is one canonical transition. `BetaOptimalityBoundary` lives in `CanonicalLearnerMonolith.agda` and is re-exported by the theorem monolith. It proves both: an exactly maximal action is beta-optimal for every additive tolerance beta; and no reward-independent fixed action is beta-optimal uniformly over all two-action reward assignments. Here beta is additive regret tolerance, not the unrelated `C.beta` layer-normalisation offset.

`CanonicalBellmanOrderTheory` keeps two non-subsuming fixed-point principles because their hypotheses differ: Tarski requires a complete meet-order plus monotonicity, whereas the iterative Kleene result requires a pointed `ω`-CPO and preservation of suprema of increasing `ω`-chains. The latter proves the least fixed point equals the supremum of bottom-starting iterates and proves order-independence/uniqueness of the least solution.

The theory now has a neural-network/MDP adapter, `NeuralPolicyMDP`. It exposes state/action/value domains, reward, discount, transition expectation, action supremum laws, the Q network and its greedy policy, and a Bellman endomap explicitly equated with the optimal backup. `neuralBellmanAtStepZero`, `neuralBellmanOptimalValueIsFixed`, and `neuralBellmanOptimalValueIsLeast` state the concrete typed conclusions. `neuralPolicyGreedyOptimalAtBellmanValue` proves one-step action optimality under exact Bellman-consistent Q values. It does **not** prove that a trained network satisfies that exactness assumption, that an arbitrary approximation is epsilon-optimal, or that the selected policy is globally optimal without the policy-evaluation/contraction conditions. Those must be supplied by a specific learner/MDP instantiation. The canonical *state transition* itself has no fixed point because its LCB total count increases at every step; it is different from the value-space Bellman map.

There are three different search/evaluation layers, not a single “A*/Q* graph search”:

- `astar` is the semantic-law capability planner. Its score is `g+h` (`g` = plan length; `h = 0` at a goal and `h = 1` otherwise). The one-step lower bound is admissible because any unfinished plan needs at least one more law insertion. A real bug was fixed here: selecting a law that covered several capabilities previously marked only the triggering capability, so later iterations incorrectly reported the remaining capabilities as uncovered while refusing to select the already-present law again. `addCapabilities` now records every capability provided by the selected law; `multiCapabilityCoverageRegression` checks one law can satisfy two required capabilities with a one-law plan. `proposalPrior` only breaks ties between equal A* scores; it is not a Bellman Q-value.
- `graphAStarFirst` is the dependency graph's best-first single-chain search. It uses unit dependency costs, JAxtar's integer-scaled score and incoming-first ties, best-`g` deduplication, stale-entry skipping, and a finite lazy fuel list. Its shortest-path guarantee is a graph-search property under the unit-cost/simple-path model, not a Q-learning result. `autonomousGraphSearchFromRoot` is a third routine: bounded DFS enumeration, not A*. Cycle/missing-dependency regressions cover selected finite examples; they are not a universal theorem for arbitrary graphs.
- The capability planner is composed with the symbolic e-graph: `canonicalSearchPlanEGraphClosed` requires its selected plan to pass saturation and costed `extractBest`. A separate `graphAStarPlanEGraphClosed` regression exercises the dependency A* path through that same boundary. E-graph saturation and extraction use the established cubic enode-count fuel budget because recursive extraction consumes fuel at multiple levels. These are executable pipeline regressions, not proofs that the named laws are true. E-graph equivalence/saturation and dependency reachability remain distinct relations. The source-signature comparison is now explicitly labelled a **candidate heuristic**: whitespace-normalized signature text is not a proof of logical implication or theorem subsumption, and candidates must never be represented as five Agda pruning proofs.

The neural MDP has a different object: `Q^*(s,a) := r(s,a) + \gamma E[V^*(s')]`, with `V^*(s) = sup_a Q^*(s,a)` under the `NeuralPolicyMDP` contract. A greedy-`nnQ` action is shown one-step optimal only under the explicit exact-Q hypothesis, plus the model's order/supremum contracts. There is no separate `qStar` graph-search algorithm; Q* is the Bellman-optimal action-value function. Do not make the theorem-dependency graph pretend to be an MDP.

The `astarWithFuel` search uses a lazy list of unit tokens of finite length `4 × n!`; generated Haskell demands the fuel spine as it runs. This affects runtime allocation/time-to-first-result, not the proof status of a missing plan. Fuel exhaustion alone never proves non-existence.

`FullCoupled/FormalMethods/MonoidLSTMStreams.agda` defines sized streams, finite-prefix fusion for map and stateful scan, and coinductive bisimulation. Those proofs establish generic stream laws; they do not yet identify every generic scan with the deployed LSTM kernel absent a model-specific instantiation.

**Hwang/Dubins–Freedman research result.** The searches narrowed the likely meaning of “Hwang’s theorem” to stable matching, with two related citations that should not be collapsed into one theorem. (1) J. S. Hwang, “On classical and modern marriage problems” (1989), DOI [10.1080/00207168908803725](https://doi.org/10.1080/00207168908803725), gives a short proof of the Dubins–Freedman “honest is the best policy” result: in the standard men-proposing deferred-acceptance setting, a coalition of men cannot all improve by jointly misreporting their preference lists. (2) Demange, Gale, and Sotomayor, “A Further Note on the Stable Matching Problem” (1987), whose abstract says a lemma of J. S. Hwang is used to generalize Dubins–Freedman, derives a form of non-manipulability for coalitions containing agents from both sides and a stronger stability property of the matching-game core. Sources: [RePEc record](https://ideas.repec.org/p/hal/journl/halshs-00670980.html) and [EconPapers record](https://econpapers.repec.org/RePEc:hal:journl:halshs-00670980). A secondary-source abstract in Huang, “Cheating to get better roommates in a random stable matching” (2007), reports the mixed-coalition variant as: no coalition of men and women can manipulate into a new stable matching in which every coalition member is strictly better off than under men-proposing Gale–Shapley; a sharper result excludes joint manipulation that makes every coalition man strictly better while no coalition woman becomes worse. The exact original Hwang lemma and all preference/reporting/stability hypotheses still need full-text verification before encoding this as a kernel theorem. This is a matching-theoretic result, not neural-network approximation. It must not be conflated with Hwang’s separate *quasi-power theorem*, which concerns asymptotic normality for random variables whose moment-generating functions have an approximate power form.

The Dubins–Freedman result surfaced by the search concerns invariant probabilities and convergence for random iterations of i.i.d. maps under splitting assumptions. `canonicalLearnerTrace` is deterministic, so that theorem does not apply unless the project defines a random transition kernel and proves the required splitting hypotheses. Gale–Shapley proposer-optimality likewise needs a finite preference/matching model, a deferred-acceptance semantics, and a stable-matching proof. It is neither implied by recurrent-stream bisimulation nor by Bellman least-fixed-point theory.

**Delay / Thunk / sized-stream boundary.** Agda2HS’s `Delay` is an explicit `now`/`later` representation with a thunked delayed tail and proof-indexed observation; it is useful for expressing delayed computations. The canonical learner currently uses its own sized `LearnerStream`, and `FormalMethods/MonoidLSTMStreams.agda` independently proves finite-prefix map/scan fusion and coinductive bisimulation. These are complementary designs, not interchangeable proof shortcuts. A delay constructor, global rewriting, confluence checks, sized types, or observational type theory does not manufacture stochasticity, matching preferences, value-order completeness, or Bellman monotonicity. Keep rewriting options file-local and the established global CLI flags unchanged.

**Integer representation.** The misleading `Int8` / `int8` wrapper is renamed `IntCode` / `intCode`; its projection is `intCodeValue`. It stores the repo’s unbounded mathematical integer, not a bounded machine byte: no overflow, wraparound, or 8-bit range invariant follows from this type name. The token encoding’s exact left inverse proves injectivity for this representation only; it is not injectivity of the GRU hidden-state readout.

## Fennel synchronization and Cubical audit (2026-10-13)

The canonical Agda import contract is declared in `.ci/agda/import-contracts.tsv` and checked by `.ci/lua/agda_import_sync.fnl`, packaged by Nix as `.#agda-import-sync`. `--sync` updates only explicitly declared import lines; `--check` is read-only. Both executable wrappers still read the one-per-line `.ci/agda/global-options.txt`. The `.#agda-emacs` package and `.#agda-emacs` development shell expose Emacs with the Nix-provided Agda mode.

The tracked Agda/Literate Agda sources have no Cubical imports, Cubical option pragmas, or listed Cubical primitives, so no proof definitions were deleted speculatively. The Fennel sync check now rejects those constructs and legacy Mirth sync markers. Reflection remains in the canonical learner where reflection is used; coinduction remains in the learner and guarded stream module where delayed/coinductive definitions use it. Reflection is intentionally outside the Agda2HS executable closure because that runtime does not construct or inspect Agda syntax trees.

This does not claim complete source-level TypeTopology retirement: the legacy theorem and logical-spec modules still use APIs previously supplied by TypeTopology. Those imports require an explicit symbol-by-symbol port plus proof repair, or a conscious decision to retire the corresponding theorem surface; deleting import lines alone would break their typechecking contract.

The `.#agda` package exposes an executable named `agda` with the centralized common flags, and `.#agda-emacs` puts that wrapper ahead of the Nix-provided Agda mode. The separate `agda2hs-agda` wrapper remains available for CI and explicit Agda2HS-specific workflows.

## Legacy option hardening (2026-10-13)

**Audit correction (2026-10-16):** the current protected `OPTIONS` prefixes of both legacy monoliths still contain `--omega-in-omega`. Agda's command-line manual explicitly says this option enables `Setω : Setω` and makes Agda inconsistent. Therefore no theorem checked only under those monolith options should be described as a sound proof. The connected CI keeps the legacy monoliths outside the pure kernel-check closure; its independent Agda2HS graph checks do not repair this trust issue. I have left the two protected `OPTIONS` prefixes and the global command untouched, as requested. The appropriate eventual resolution is a separately reviewed option-profile change plus re-checking imports/proofs, not pretending the current profile is consistent.

The current monolith prefixes also retain `--large-indices` with `--no-forced-argument-recursion` and `--with-K`. The Agda manual warns about `--large-indices` paired with **enabled** forced-argument recursion or `--without-K`; the current pair avoids those two exact combinations, at the cost of losing termination-checker power from forced arguments. The previous text claiming that `--omega-in-omega` had been removed was wrong and is replaced here.

Flag-use audit from the source:
- `--sized-types` has a concrete use: `LearnerStream` decreases its tail index via `Size<`, and finite observations are related to `iterateCanonical`.
- `--rewriting` has explicit rewrite rules in `CanonicalLearnerMonolith.agda` (e.g. list/map, eliminator, transport, and coercion rules); the theorem monolith currently declares no `REWRITE` rules of its own. `--confluence-check` is therefore relevant to the canonical file, although the legacy full monolith still is not typechecked in the active pure-kernel lane.
- `--prop` is explicitly used to encode the `prop` constructor in the metaprogramming/reflection AST and register `AGDASORTPROP`. That is correct for syntax representation; it does not by itself show that the learner's semantic propositions are declared in `Prop`.
- `--flat-split` has no visible `@♭` pattern use in these two files, and no user `POLARITY` pragmas were found; those flags appear not to drive the target definitions directly.
- `--cumulativity`, `--level-universe`, `--auto-inline`, `--two-level`, `--exact-split`, and erasure settings affect elaboration/typechecking/extraction globally within each file. No theorem-specific proof depends on a corresponding named function or tactic; keep them only as the established legacy profile unless a separately checked minimal profile is developed.
- The command-line manual documents `--with-K` as an identity-type assumption that is incompatible with importing the cited `--without-K` circle/Pushout theory as if it shared the same type theory. Those files must remain isolated behind a compatible module/profile.

This flag audit does **not** certify either legacy monolith. They remain source inventory until a sound option profile and a complete typecheck path are established; the active pure Agda2HS modules are independently kernel-checked.

The shared `.ci/agda/global-options.txt` contains only `--erasure`, `--no-projection-like`, and CLI verbosity. The legacy monoliths retain their own elaboration profile in file-local OPTIONS; forcing those flags onto imports such as `agda2hs-base` changes universe and instance checking and can break Agda's safe-module boundary. The Nix wrappers copy `agda2hs-base` to a temporary writable source tree before checking so Agda can write interfaces without modifying the immutable Nix store.


## Backend choice, lazy demand, inversion, and refinement checking

- **Agda2HS → GHC is the current verified extraction path.** Agda2HS intentionally extracts a typed common subset into readable Haskell and erases proof-only material; it does not compile arbitrary Agda. The connected flake uses the Agda2HS base library, compiles generated Haskell with GHC `-dcore-lint`, and declares `plugins=none` in the semantic-search manifest. That is compiler/Core sanity plus executable regression, not an automatic Haskell proof of the Agda theorem.
- **Liquid Haskell is not currently extracting theorem properties from Agda2HS.** The Nix pipeline puts the `liquid` executable on PATH and runs `liquid --version`; it does not invoke Liquid Haskell on generated modules or load an LH GHC plugin. Refinement properties would need Haskell-side annotations/specifications against the generated API and an explicit `liquid` verification command. Good follow-up candidates are non-empty search result invariants, best-`g` monotonicity, and bounded graph-path validity. Lazy evaluation must remain part of the specification; a refinement about a value being evaluated cannot be silently assumed for an unevaluated thunk.
- **Haskell⁻¹ is useful for exploration, not proof.** Teegen, Prott, and Bunkenburg's “Haskell⁻¹: automatic function inversion in Haskell” describes a GHC plugin that extends the functional model with nondeterminism and free variables to generate inverse functions. It could help enumerate candidate witnesses or reverse-search small executable kernels. Its nondeterministic search result does not establish Agda propositions, confluence, soundness of the neural semantics, or global optimality. Keep such results as examples/counterexample candidates, then formalize the relation and proof in Agda.
- **Agda2Scheme status and benchmarks.** Its upstream README still describes the Chez Scheme backend as work in progress. The inspected Cabal package requires Agda `>= 2.8` but declares only an executable; it has no `benchmark-suite`, and the CI's `--enable-benchmarks` flag alone does not create one. There is no upstream benchmark result in that repo and no Agda2Scheme benchmark in this project. So there is no measured basis to claim it is faster than Agda2HS/GHC here. Its potential use is a separate experiment after compatibility tests; compare cold compile time, warm runtime, allocation, laziness behaviour, generated-code size and proof-feature coverage on the same finite fixtures.
- **A* versus Q*.** JAxtar-compatible graph A* is the appropriate implementation for minimum-cost law/dependency plans, because this domain has graph edges and path costs but no reward transition kernel. Q-learning/Q* applies to the neural MDP layer and uses rewards, transitions, and Bellman backups. The new `NeuralPolicyMDP` contract makes that layer explicit; do not make the theorem-dependency graph masquerade as an MDP.
- **Demand semantics matter, with a boundary.** The extracted Haskell factorial-fuel list is lazy, so A* can demand its spine incrementally and avoid eager allocation of `4 × n!` cells. This affects runtime allocation and time-to-first-result. It does not turn finite fuel into an infinite stream or prove that exhaustion means no solution. The sized `LearnerStream` theorem proves finite observation and coinductive fusion; a theorem about Haskell call-by-need allocation requires an operational/cost model of the generated Haskell, not just stream bisimulation in Agda.

Research pointers: [Agda2HS paper](https://doi.org/10.1145/3546189.3549920); [Haskell⁻¹ paper record](https://dblp.org/rec/conf/haskell/TeegenPB21.html); [Liquid Haskell, refinement types and lazy evaluation](https://doi.org/10.1145/2628136.2628161); [Agda2Scheme repository](https://github.com/jespercockx/agda2scheme).
