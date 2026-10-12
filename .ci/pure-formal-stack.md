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

## Current migration state (2026-10-12)

The repository is **not yet fully TypeTopology-free**. `flake.nix` pins `typetopology`, and `FullCoupled/TheoremsMonolith.agda` and `FullCoupled/LearnerLogicalSpec.agda` import TypeTopology arithmetic, MLTT, UF/univalence, ordinal, and searchable-type modules. Removing the Nix input before migrating those interfaces would break the proof build. The current Agda2HS search module uses the Haskell-compatible subset, but its graph input is still produced from the TypeTopology-dependent theorem monolith in the Nix semantic app.

## Migration gates

1. **Lock down graph semantics.** Check linear-chain order, independent siblings, unique path identifiers, missing dependencies, cycle termination policy, score ordering, and finite fuel bounds. Generate the graph fixture deterministically; do not infer proof validity from a dependency edge.
2. **Separate runtime graph input.** Export a stable, versioned graph snapshot or simple edge manifest. Make the Agda2HS search app consume that artifact. Keep Agda dependency-graph generation and theorem-kernel checking in their own proof lane. Validate artifact schema, source revision, and hash.
3. **Retire TypeTopology in slices.** Inventory each imported symbol and dependent theorem. Port only the required interfaces into owned, auditable modules (or a deliberately chosen pinned library), then prove replacement lemmas. Remove `typetopology` from `flake.nix` only when no source or command references remain and all kernel lanes pass without its include path.
4. **Add sidecars reproducibly.** Add Acorn, XDS-Agda, and Mini-Vehicle/Vehicle lanes only after their toolchains are pinned and smoke-tested. Do not add an unpinned network installer or a speculative Nix package merely to make a flake look complete.
5. **Require closure proof.** CI must build from a clean checkout and verify the search fixtures, Agda kernel gates, Haskell extraction/GHC checks, sidecar assumptions, and generated manifests. Report each lane as pass, fail, unavailable, or blocked. Do not collapse them into one green Boolean.

The target is a small executable core plus explicitly separated proof sidecars. Full TypeTopology retirement is a gated migration, not a dependency deletion that leaves theorem imports unresolved.
