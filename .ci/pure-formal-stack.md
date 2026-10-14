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

The checked starter module is `FullCoupled/FormalMethods/ScottStracheyDomains.agda`. It distinguishes `bottom` from the defined numeric zero and interprets a small language of numerals, divergence, and strict addition. Its counterexamples show that strict lifted operations do not, in general, give a ring or semiring over the *whole lifted carrier*; this does not imply a defect in the unlifted integers, rationals, or reals.

This is an executable starter model—not yet a full CPO/Scott-continuity/fixed-point theorem. A complete account still needs chain suprema, monotonicity/continuity proofs, and a least-fixed-point construction for recursive search. The graph/A* implementation remains a separate executable algorithm with bounded runtime regressions.

`FullCoupled/FormalMethods/MonoidLSTMStreams.agda` is the isolated guarded stream layer: it defines delayed streams, suffix duplication/extension, a coinductive bisimulation relation, and finite-prefix causality proofs for mapping and stateful scans. The scan is an interface for the concrete LSTM recurrence, not yet a proof about the repository's deployed model. Reflection is not imported because these definitions do not inspect or construct Agda syntax trees.

## Fennel synchronization and Cubical audit (2026-10-13)

The canonical Agda import contract is declared in `.ci/agda/import-contracts.tsv` and checked by `.ci/lua/agda_import_sync.fnl`, packaged by Nix as `.#agda-import-sync`. `--sync` updates only explicitly declared import lines; `--check` is read-only. Both executable wrappers still read the one-per-line `.ci/agda/global-options.txt`. The `.#agda-emacs` package and `.#agda-emacs` development shell expose Emacs with the Nix-provided Agda mode.

The tracked Agda/Literate Agda sources have no Cubical imports, Cubical option pragmas, or listed Cubical primitives, so no proof definitions were deleted speculatively. The Fennel sync check now rejects those constructs and legacy Mirth sync markers. Reflection remains in the canonical learner where reflection is used; coinduction remains in the learner and guarded stream module where delayed/coinductive definitions use it. Reflection is intentionally outside the Agda2HS executable closure because that runtime does not construct or inspect Agda syntax trees.

This does not claim complete source-level TypeTopology retirement: the legacy theorem and logical-spec modules still use APIs previously supplied by TypeTopology. Those imports require an explicit symbol-by-symbol port plus proof repair, or a conscious decision to retire the corresponding theorem surface; deleting import lines alone would break their typechecking contract.

The `.#agda` package exposes an executable named `agda` with the centralized common flags, and `.#agda-emacs` puts that wrapper ahead of the Nix-provided Agda mode. The separate `agda2hs-agda` wrapper remains available for CI and explicit Agda2HS-specific workflows.

## Legacy option hardening (2026-10-13)

Removed `--type-in-type`, `--no-termination-check`, `--no-positivity-check`, and `--no-fast-reduce` from the two legacy learner source pragmas. Also removed `--large-indices` together with `--forced-argument-recursion`: the Agda manual documents that pair as inconsistent. `--omega-in-omega` is deliberately prohibited because it enables `Setω : Setω` and makes Agda inconsistent. The CI Nix-surface script now guards against reintroducing these options.

This hardening does **not** certify either legacy monolith: they still contain TypeTopology-era imports and are excluded from the current kernel-check lane. They remain source inventory until those imports and dependent proofs are ported and a clean kernel check is added. The active pure Agda2HS modules are independently kernel-checked. Do not describe this source change alone as a proof result.

The shared `.ci/agda/global-options.txt` contains only `--erasure`, `--no-projection-like`, and CLI verbosity. The legacy monoliths retain their own elaboration profile in file-local OPTIONS; forcing those flags onto imports such as `agda2hs-base` changes universe and instance checking and can break Agda's safe-module boundary. The Nix wrappers copy `agda2hs-base` to a temporary writable source tree before checking so Agda can write interfaces without modifying the immutable Nix store.
