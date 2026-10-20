{-
PROJECT CONTRACT — canonical documentation, constraints, and workflow plan

Proof placement:
  * Non-graph-search theorem proofs live only in
    FullCoupled/CanonicalLearnerMonolith.agda and
    FullCoupled/TheoremsMonolith.agda.
  * Graph-search/e-graph definitions and regressions live in the graph-specific
    Agda2HS modules and graph checker.
  * Do not add standalone non-graph-search proof modules, reflection helpers,
    proof sidecars, or custom prover dependencies.

Real arithmetic:
  * Keep the Agda2HS compiler unmodified and sourced from Nixpkgs. The
    Acorn exact-real library is not integrated: its upstream build pins a
    modified Agda2HS fork and an older Agda API, which violates this project's
    official-Nixpkgs-only toolchain rule. Do not substitute a hand-written
    Cauchy interface and claim equivalence with Acorn/CoRN. Reconsider Acorn
    only if it builds against the unmodified Nixpkgs Agda2HS package.
  * Do not mix compiled Haskell artifacts across incompatible GHC package sets.

Graph semantics:
  * Distinguish the Agda import DAG, law-dependency paths, and symbolic e-graph.
    None is a proof term or evidence that a theorem's statement is true.
  * Production graphAStarFirst stays eager A*. Its current score is
    999999*g + 1000000*h, ties insert incoming-first, and best-g is indexed by
    law ID. These choices mirror parts of JAxtar's standard A* semantics, not
    JAxtar's batched JAX execution.
  * Deferred A* is not production until Agda proves its full contract is not
    inferior on the supported graph class, including path validity, duplicate
    and cycle behavior, result cost, and fuel exhaustion. Benchmark before
    claiming faster execution. Finite regressions do not prove general
    optimality.
  * DAG chain counting uses topological dynamic programming, avoiding
    exponential path-list construction. Dependency closure separately gathers
    reachable nodes and topologically orders them, rejecting missing names
    and cycles. Path enumeration remains fuel-bounded; CI fixtures establish
    correctness, not runtime performance.
  * Keep eager A* for first-path search when a heuristic is useful. JAxtar
    provides batched JAX A*/Q* for accelerator-backed, neural-heuristic search;
    Mctx provides JAX Monte Carlo tree search over learned policy/value and
    dynamics models. Neither replaces exact dependency closure or cycle
    rejection. Do not add either runtime to the Agda/Nix graph checker without
    a separate workload and reproducible benchmark.
    References: https://github.com/tinker495/JAxtar and
    https://github.com/google-deepmind/mctx.

Constructive foundations — Russian constructivism (RUSS) only:
  * Status: NOT GLOBALLY CERTIFIED. Certification requires a checked theorem-
    dependency inventory, not just references, builds, or source-text searches.
  * RUSS uses intuitionistic logic with scoped recursive/computability
    assumptions. Markov's principle and register-machine Church's thesis are
    explicit assumptions, not a blanket grant of classical logic. Proposition-
    valued countable choice is an additional project assumption whose
    compatibility with the chosen RUSS formalization must be justified.
    Do not add excluded middle, LPO, or LLPO as global axioms.
  * Audit every project-owned postulate and primitive, every REWRITE rule,
    Agda builtin/reflection/TC interface, termination/positivity/universe
    option, imported trusted theorem, unresolved meta, and transitive theorem
    dependency. Every exported theorem must depend only on declared RUSS
    assumptions and separately justified Agda/compiler primitives. Any
    unclassified trust boundary blocks global certification.
  * The learner monolith includes Markov, register-machine Church's thesis,
    and proposition-valued countable choice. The theorem monolith contains
    Agda reflection/TC compatibility postulates and imports external ordinal
    and TWA modules. These remain trust boundaries, not a consistency proof;
    successful builds are necessary but insufficient.
  * Both monoliths explicitly use --with-K. Keep their proof path non-cubical:
    no Cubical imports or Cubical modes. Agda's --cubical option enables
    --without-K, which conflicts with this project's selected path. Some
    Agda option combinations are more nuanced, so this is a project mode
    decision, not a claim that every Cubical development is incompatible with
    every use of K.
  * Impredicative higher-inductive encodings remain literature-only. Their
    compatibility with --with-K and the project's RUSS assumptions is unproved;
    no such encoding is part of the current formal dependency graph.
  * Maintain one Russian-constructivist review track; do not add a second
    constructive foundation profile or gate. Audit actual assumptions and
    dependencies rather than classifying a school of thought as a proof rule.
  * The former O(n^2) signature-matching redundancy scan was removed because
    identical signature text does not prove logical implication. Delete theorem
    statements only after typed proof/dependency review and repository-wide
    reference analysis establish genuine redundancy.

  References:
    - Stanford Fall 2024 archived edition of Constructive Mathematics:
      https://plato.stanford.edu/archives/fall2024/entries/mathematics-constructive/
    - Douglas Bridges and Fred Richman, Varieties of Constructive Mathematics,
      Chapter 3, "Russian Constructive Mathematics" (Cambridge University Press):
      https://doi.org/10.1017/CBO9780511565663.004
    - Hannes Diener, Constructive Reverse Mathematics (2018):
      https://arxiv.org/abs/1804.05495
    - Leon Henkin, The Completeness of the First-Order Functional Calculus (1949):
      https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/completeness-of-the-firstorder-functional-calculus/2F7FFE04841B89975F5EA447A01481CD
    - F. William Lawvere, Diagonal Arguments and Cartesian Closed Categories (1969):
      https://doi.org/10.1007/BFB0080769
    - Pierre-Marie Pédrot and Nicolas Tabareau, Failure is not an option — an exceptional type theory:
      https://doi.org/10.1007/978-3-319-89884-1_9
    - Agda compiler source and project history:
      https://github.com/agda/agda
    - Agda 2.8 Postulates:
      https://agda.readthedocs.io/en/v2.8.0/language/postulates.html
    - Agda 2.8 Safe Agda:
      https://agda.readthedocs.io/en/v2.8.0/language/safe-agda.html
    - Agda 2.8 Rewriting:
      https://agda.readthedocs.io/en/v2.8.0/language/rewriting.html
    - Agda Without-K and identity-elimination options:
      https://agda.readthedocs.io/en/v2.8.0/language/without-k.html
    - The Taming of the Rew, rewriting rules, confluence and subject reduction:
      https://doi.org/10.1145/3434341
    - XDS-Agda, mechanised Scott–Strachey denotational semantics:
      https://pdmosses.github.io/xds-agda/
    - nLab, domain theory (only for the existing Scott–Ershov semantics context):
      https://ncatlab.org/nlab/show/domain%2Btheory
    - Higher Inductive Types Via Impredicative Encodings (research candidate only):
      https://eprints.illc.uva.nl/id/eprint/2381/
    - MtacAR, monadic typed tactic programming in Agda by reflection (research prototype only):
      https://github.com/L-TChen/MtacAR
    - Streamly Hackage package, used for Haskell stream-processing context:
      https://hackage-content.haskell.org/package/streamly
    - Hackage agda2hs package:
      https://hackage-content.haskell.org/package/agda2hs-1.4
    - agda2hs documentation:
      https://agda.github.io/agda2hs/
    - Martín Escardó and collaborators, TypeTopology Agda development (external theorem context):
      https://martinescardo.github.io/agda-new/
    - Nicolai Kraus et al., Type-Theoretic Approaches to Ordinals:
      https://arxiv.org/abs/2208.03844

  Source notes:
    The archived Stanford entry and Bridges/Richman chapter ground the RUSS
    discussion; Diener's paper supplies reverse-mathematics comparisons, not
    certification of this repository.
    Henkin's first-order completeness construction and Lawvere's fixed-point
    theorem are distinct results joined only as an audit-closure target; no
    implication between them is asserted without a separate proof.
    XDS-Agda formalises Scott–Strachey semantics but declares postulates, so it
    is context rather than trusted proof evidence. nLab domain theory is
    relevant to the existing Scott–Ershov denotational-semantics section.
    "The Taming of the Rew" motivates checking rewrite confluence and subject
    reduction. Agda manuals/repository and agda2hs documentation describe the
    implementation, rewrite, and extraction trust boundaries.
    MtacAR is a research prototype, not an imported dependency or a certificate
    of the project's reflection/TC postulates. The impredicative-HIT paper is
    a candidate for study only; compatibility with --with-K and RUSS remains
    unproved. The project deliberately avoids Cubical mode/imports in its
    --with-K proof path; Agda's --cubical option enables --without-K.
    Streamly is used by the flake for Haskell stream processing. TypeTopology
    and ordinal papers are external-context pointers,
    not evidence that transitive dependencies have a checked --with-K closure.
    The archived Stanford entry is a dated source, not independent corroboration.
    Global RUSS certification remains blocked until every trusted interface and
    transitive dependency is classified.
Lua/Elm:
  * Keep Fennel for orchestration and use the pinned Luafun module directly.
    Fennel and MoonScript can call ordinary Lua libraries; Teal can too but
    typed coverage for Luafun requires a maintained declaration file.
  * .ci/lua/agda_graph.fnl produces GeneratedAgdaGraph.elm. Luafun applies to
    that Fennel generator; Elm itself does not load the Lua library.
  * Pages/Elm must be validated by the existing Nix presentation lane.

Only this file owns project policy text and lane commands. The GitHub workflow
YAML files are runners which invoke these Dhall lanes; do not maintain a second
set of prose requirements in Markdown.
-}

let policyGate = ''
  set -euo pipefail
  # Canonical contract and proof-placement policy.
  test -f .ci/actions_ci.dhall
  test ! -e .ci/pure-formal-stack.md
  test ! -e .ci/graph-search-contract.md
  test ! -e .ci/discovery/graph-search-spec.md
  test ! -e FullCoupled/ReflectionAutomation.agda
  test ! -e FullCoupled/FiniteTabularUAP.agda
  test ! -e FullCoupled/CircleHITInterface.agda
  grep -Fq 'agda2hsTool = system:' flake.nix
  grep -Fq '(pkgsFor system).haskellPackages.agda2hs' flake.nix
  grep -Fq 'graphAStarFirst :' FullCoupled/Agda2HsSemanticSearch.agda
  grep -Fq 'graphAStarFirst laws seed = graphAStarFirstEager laws seed' FullCoupled/Agda2HsSemanticSearch.agda
  grep -Fq 'graphAStarDeferredPriorityLowerBoundRegressionChecked' FullCoupled/Agda2HsSemanticSearch.agda
  grep -Fq 'graphAStarDeferredMatchesEagerRegressionChecked' FullCoupled/Agda2HsSemanticSearch.agda
  grep -Fq 'russianRecursiveMathematicsAssumptions' FullCoupled/CanonicalLearnerMonolith.agda
  grep -Fq 'open ConstructiveComputabilityPostulates public using' FullCoupled/CanonicalLearnerMonolith.agda
  grep -Fq 'Type = Term' FullCoupled/TheoremsMonolith.agda
  grep -Fq 'abs : String → A → Abs A' FullCoupled/TheoremsMonolith.agda
  grep -Fq -- '--with-K' FullCoupled/CanonicalLearnerMonolith.agda
  grep -Fq -- '--with-K' FullCoupled/TheoremsMonolith.agda
  ! grep -Eq '^[[:space:]]*--cubical(=|$)' FullCoupled/CanonicalLearnerMonolith.agda
  ! grep -Eq '^[[:space:]]*--cubical(=|$)' FullCoupled/TheoremsMonolith.agda
  ! grep -Eq '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Cubical([.]|[[:space:]]|$)' FullCoupled/CanonicalLearnerMonolith.agda
  ! grep -Eq '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Cubical([.]|[[:space:]]|$)' FullCoupled/TheoremsMonolith.agda
  ! grep -Fq 'GuardedCubical' FullCoupled/TheoremsMonolith.agda
  ! grep -Fq 'cubical=no-glue' FullCoupled/TheoremsMonolith.agda
''

let Lane = < AgdaLearner | AgdaTheorem | AgdaSafe | Agda2Hs | FennelPresentation | Pages | Discovery | EconlibCrossrepo | EconlibEquilibriumSearch | StrictExistenceImpossibility | StationaryCycleImpossibility | IsomorphismTransport | SemanticContract | Surface | Versions | AutoMerge | All >

let lane : Lane = env:CI_LANE

let script = merge {
  AgdaLearner = ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSurface.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSemanticExtractor.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsTheoremGraphEGraph.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSemanticSearch.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsGraphSearchCheck.agda
    # The legacy monolith's --level-universe option is intentionally not
    # kernel-checked through Haskell.Prelude: Agda rejects that mixed option
    # closure. Keep source inventory separate from the pure executable kernel
    # surface until its universe/Prelude interfaces are migrated coherently.
    grep -Fq 'module FullCoupled.CanonicalLearnerMonolith' FullCoupled/CanonicalLearnerMonolith.agda
    grep -Fq -- '--level-universe' FullCoupled/CanonicalLearnerMonolith.agda
    echo "pure-agda2hs-kernel-check=pass"
    echo "canonical-learner-monolith=source-inventory-only (option closure not kernel-checked)"
    '',
  AgdaTheorem = ''
    set -euo pipefail
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSurface.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSemanticExtractor.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsTheoremGraphEGraph.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSemanticSearch.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsGraphSearchCheck.agda
    grep -Fq 'graphDependencyOrderRegressionChecked = refl' FullCoupled/Agda2HsSemanticSearch.agda
    grep -Fq 'graphTwoLeafBranchesRegressionChecked = refl' FullCoupled/Agda2HsSemanticSearch.agda
    grep -Fq 'graphCycleIsRejectedRegressionChecked = refl' FullCoupled/Agda2HsSemanticSearch.agda
    grep -Fq 'sourceOnlyLegacyBoundaryRegressionChecked = refl' FullCoupled/Agda2HsSemanticSearch.agda
    echo "TheoremsMonolith=source-inventory-only"
    '',
  AgdaSafe = ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSurface.agda
    echo "agda-safe=checked-pure-surface; legacy-monoliths=not-in-pure-kernel-target"
    '',
  Agda2Hs = ''
    set -euo pipefail
    nix run .#agda-haskell-pipeline
    test -s build/agda-haskell/FullCoupled/Agda2HsSurface.hs
    test -s build/agda-haskell/agda2hs-manifest.tsv
    echo "agda2hs=pass"
    echo "agda2hs-plugins=none"    '',
  FennelPresentation = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    mkdir -p "$tmp/src"
    test -f .ci/lua/agda_graph.fnl
    test -f .ci/lua/agda_surface.fnl
    test -f .ci/lua/ascii_surface.fnl
    nix run .#fennel-ascii-surface
    nix run .#fennel-agda-graph -- "$tmp/src/GeneratedAgdaGraph.elm"
    test -s "$tmp/src/GeneratedAgdaGraph.elm"
    grep -Fq 'module GeneratedAgdaGraph exposing (Node, Edge, nodes, edges)' "$tmp/src/GeneratedAgdaGraph.elm"
    grep -Fq 'FullCoupled.TheoremsMonolith' "$tmp/src/GeneratedAgdaGraph.elm"
    nix run .#fennel-surface -- "$tmp/src/GeneratedTheoremSurface.elm"
    test -s "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'siteTitle : String' "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'nodeLines : List String' "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'edgeLines : List String' "$tmp/src/GeneratedTheoremSurface.elm"
    if LC_ALL=C grep -n '[^[:print:][:space:]]' "$tmp/src/GeneratedTheoremSurface.elm"; then exit 1; fi
    echo "fennel-luajit-presentation=pass"
    '',
  Pages = ''
    set -euo pipefail
    grep -Fq 'open import Haskell.Prelude' FullCoupled/Agda2HsSemanticSearch.agda
    ! grep -Eiq '^import Unsafe[.]Haskell|^open import (Naturals|MLTT[.]|UF[.]|TWA[.])' FullCoupled/Agda2HsSemanticSearch.agda
    grep -Fq 'open import Haskell.Prelude' FullCoupled/Agda2HsSemanticExtractor.agda
    ! grep -Eiq '^import Unsafe[.]Haskell|^open import (Naturals|MLTT[.]|UF[.]|TWA[.])' FullCoupled/Agda2HsSemanticExtractor.agda
    grep -Fq 'open import Haskell.Prelude' FullCoupled/Agda2HsTheoremGraphEGraph.agda
    ! grep -Eiq '^import Unsafe[.]Haskell|^open import (Naturals|MLTT[.]|UF[.]|TWA[.])' FullCoupled/Agda2HsTheoremGraphEGraph.agda
    grep -Fq 'requiredPlanComplete' FullCoupled/Agda2HsSemanticSearch.agda
    grep -Fq 'import FullCoupled.Agda2HsSemanticExtractor as Extractor' FullCoupled/Agda2HsSemanticSearch.agda
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    grep -Fq 'module FullCoupled.CanonicalLearnerMonolith' FullCoupled/CanonicalLearnerMonolith.agda
    grep -Fq 'module FullCoupled.TheoremsMonolith' FullCoupled/TheoremsMonolith.agda
    dhall type --file .ci/presentation-contract.dhall >/dev/null
    dhall-to-json --file .ci/presentation-contract.dhall > "$tmp/presentation-contract.json"
    grep -Fq '"graphGenerator": ".ci/lua/agda_graph.fnl"' "$tmp/presentation-contract.json"
    grep -Fq '"surfaceGenerator": ".ci/lua/agda_surface.fnl"' "$tmp/presentation-contract.json"
    grep -Fq '"elmManifest": ".ci/elm-application.dhall"' "$tmp/presentation-contract.json"
    grep -Fq '"siteEntry": "index.html"' "$tmp/presentation-contract.json"
    grep -Fq '"compiledElm": "elm.js"' "$tmp/presentation-contract.json"
    grep -Fq '"asciiGenerator": ".ci/lua/ascii_surface.fnl"' "$tmp/presentation-contract.json"
    grep -Fq 'Atkinson Hyperlegible Mono' site/Main.elm
    grep -Fq 'Iosevka' site/Main.elm
    grep -Fq 'https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible+Mono' site/Main.elm
    ! grep -Eiq 'Writer|Julia[[:space:]]Mono|JuliaMono|Noto Emoji' site/Main.elm
    grep -Fq 'CAT02LMS' site/Main.elm
    grep -Fq '.shell{min-height:100vh;display:block;max-width:76ch;' site/Main.elm
    grep -Fq 'Formal-methods reading trail' site/Main.elm
    grep -Fq 'Browse modules' site/Main.elm
    grep -Fq 'Haskell denotational semantics' site/Main.elm
    ! grep -Fq 'Mirth' site/Main.elm
    grep -Fq 'maximin' site/Main.elm
    grep -Fq 'data-module' site/Main.elm
    output_dir="$tmp"
    if [ -n "$(printenv PAGES_OUTPUT_DIR 2>/dev/null || true)" ]; then
      output_dir="$(printenv PAGES_OUTPUT_DIR)"
    fi
    mkdir -p "$output_dir"
    mkdir -p "$tmp/src"
    cp site/Main.elm "$tmp/src/Main.elm"
    echo "pages-stage=fennel-graph"
    nix run .#fennel-agda-graph -- "$tmp/src/GeneratedAgdaGraph.elm"
    echo "pages-stage=fennel-graph-done"
    echo "pages-stage=fennel-surface"
    nix run .#fennel-surface -- "$tmp/src/GeneratedTheoremSurface.elm"
    echo "pages-stage=fennel-surface-done"
    test -s "$tmp/src/GeneratedAgdaGraph.elm"
    test -s "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'siteTitle : String' "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'nodeLines : List String' "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'FullCoupled.CanonicalLearnerMonolith' "$tmp/src/GeneratedAgdaGraph.elm"
    grep -Fq 'FullCoupled.TheoremsMonolith' "$tmp/src/GeneratedAgdaGraph.elm"
    grep -Fq 'imports' "$tmp/src/GeneratedAgdaGraph.elm"
    dhall-to-json --file "$GITHUB_WORKSPACE/.ci/elm-application.dhall" > "$tmp/elm.json"
    sed -i -e 's/"source_directories"/"source-directories"/g' -e 's/"elm_version"/"elm-version"/g' -e 's/"elm_dependencies"/"dependencies"/g' -e 's/"test_dependencies"/"test-dependencies"/g' "$tmp/elm.json"
    test -s "$tmp/elm.json"
    cd "$tmp"
    elm make src/Main.elm --optimize --output "$output_dir/elm.js"
    test -s "$output_dir/elm.js"
    echo "pages-build=pass"
    '',
  Discovery = ''
    set -euo pipefail
    nix run .#agda2hs-semantic-search
    report=build/agda2hs-semantic-search/report.txt
    manifest=build/agda2hs-semantic-search/agda2hs-semantic-search-manifest.tsv
    test -s "$report"
    test -s "$manifest"
    grep -E '^theorem-graph-edges=[1-9][0-9]* autonomous-depth-first-chains=[1-9][0-9]*$' "$report"
    grep -E '^agda2hs autonomous theorem-graph DFS: [1-9][0-9]* maximal dependency chains$' "$report"
    grep -Fq 'autonomous-regression=True' "$report"
    grep -Fq 'graph-branch-regression=True' "$report"
    grep -Fq 'graph-two-leaf-paths=True' "$report"
    grep -Fq 'graph-cycle-rejected=True' "$report"
    grep -Fq 'graph-path-count-dp=True' "$report"
    grep -E '^semantic-laws=[1-9][0-9]* nonreflexive=[1-9][0-9]* composite=[1-9][0-9]*$' "$report"
    grep -E '^required-plan-count=[1-9][0-9]* required-plan-total=[1-9][0-9]* required-plan-regression=True$' "$report"
    grep -Fq 'egraph-regression=True egraph-associativity-regression=True' "$report"
    grep -Fq 'canonical-search-egraph-closed=True' "$report"
    grep -Fq 'haskell-minus-one-A*=2 proof-backed laws; legacy monolith excluded from pure build' "$report"
    grep -E '^agda2hs-semantic-port=heuristic-signature-scan-disabled; [1-9][0-9]*/[1-9][0-9]* required plans dependency-closed; bulk-plan-e-graph-saturation=skipped; learner-obligation-roots=[0-9]+; learner-static-graph=(True|False)$' "$report"
    grep -Fq 'proofKernel=Agda' "$manifest"
    grep -Fq 'searchKernel=Agda2Hs' "$manifest"
    grep -Fq 'legacyMonoliths=source-scan-only' "$manifest"
    nix run .#agda2hs-graph-search-check
    nix run .#scott-strachey-domain-check
    nix run .#monoid-lstm-stream-check
    echo 'agda-semantic-discovery=pass'
    '',  EconlibCrossrepo = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"
    econlib_rev=$(git -C "$tmp/Econlib" rev-parse HEAD)

    upstream_economy="$tmp/Econlib/Econlib/Equilibrium/Economy.lean"
    upstream_existence="$tmp/Econlib/Econlib/Equilibrium/Existence.lean"
    upstream_markov="$tmp/Econlib/EconlibExamples/Equilibrium/MarkovStationary.lean"
    local_theorem="FullCoupled/TheoremsMonolith.agda"

    grep -Fq 'structure WalrasianEquilibrium' "$upstream_economy"
    grep -Fq 'theorem exists_equilibrium' "$upstream_existence"
    grep -Fq 'Nonempty E.WalrasianEquilibrium' "$upstream_existence"
    grep -Fq 'stationary Walrasian equilibrium' "$upstream_markov"

    grep -Fq 'GeneralizedWalrasianData' "$local_theorem"
    grep -Fq 'MegaGeneralizedWalrasianEquilibrium' "$local_theorem"
    grep -Fq 'GeneralizedWalrasianExistence' "$local_theorem"
    grep -Fq 'CanonicalLearnerHodgeMaxwellCompositionTheorem' "$local_theorem"
    grep -Fq 'CanonicalLearnerHodgeMaxwellCompositionTheorem' "$local_theorem"

    adapter_present=false
    adapter_dhall=False
    if grep -Eiq 'Econlib|exists_equilibrium' "$local_theorem"; then
      adapter_present=true
      adapter_dhall=True
    fi
    case "$adapter_dhall" in
      True|False) ;;
      *) echo "invalid Dhall Boolean: $adapter_dhall"; exit 1 ;;
    esac

    mkdir -p .ci/discovery
    {
      printf '%s\n' '{'
      printf '  econlib_repo = "danlyng/Econlib",\n'
      printf '  econlib_commit = "%s",\n' "$econlib_rev"
      printf '  upstream_static_existence = "Economy.exists_equilibrium",\n'
      printf '  upstream_equilibrium_object = "Economy.WalrasianEquilibrium",\n'
      printf '  local_mega_equilibrium_target = "GeneralizedWalrasianExistence",\n'
      printf '  local_composition_target = "CanonicalLearnerHodgeMaxwellCompositionTheorem",\n'
      printf '  local_mega_edge = "MegaGeneralizedWalrasianEquilibrium",\n'
      printf '  adapter_present = %s,\n' "$adapter_dhall"
      printf '  composition_path = ["Econlib::Economy.exists_equilibrium", "Actions::MegaGeneralizedWalrasianEquilibrium", "Actions::CanonicalLearnerHodgeMaxwellCompositionTheorem"],\n'
      printf '  graph_status = "composition-ready; explicit cross-language adapter still required"\n'
      printf '%s\n' '}'
    } > .ci/discovery/econlib-crossrepo-sync.dhall

    dhall text --file .ci/discovery/econlib-crossrepo-sync.dhall >/dev/null
    grep -Fq 'upstream_static_existence = "Economy.exists_equilibrium"' .ci/discovery/econlib-crossrepo-sync.dhall
    grep -Fq 'local_composition_target = "CanonicalLearnerHodgeMaxwellCompositionTheorem"' .ci/discovery/econlib-crossrepo-sync.dhall
    echo "econlib-crossrepo-sync=pass"
    echo "econlib-commit=$econlib_rev"
    echo "adapter-present=$adapter_present"
    '',
  EconlibEquilibriumSearch = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"
    econlib_rev=$(git -C "$tmp/Econlib" rev-parse HEAD)

    root="$tmp/Econlib"
    local_theorem="FullCoupled/TheoremsMonolith.agda"

    files=(
      "$root/Econlib/Equilibrium/Economy.lean"
      "$root/Econlib/Equilibrium/Existence.lean"
      "$root/Econlib/Equilibrium/AggregateAccounting.lean"
      "$root/Econlib/Probability/Markov/Ergodic.lean"
      "$root/Econlib/GameTheory/ExtensiveForm/Core/Strategy.lean"
      "$root/Econlib/GameTheory/ExtensiveForm/Refinements/BeliefSystem.lean"
      "$root/Econlib/GameTheory/ExtensiveForm/Refinements/SequentialEquilibrium.lean"
    )
    for f in "''${files[@]}"; do
      [ -f "$f" ] || { echo "missing upstream graph file: $f"; exit 1; }
    done

    grep -Fq 'RegularEconomy' "$root/Econlib/Equilibrium/Existence.lean"
    grep -Fq 'theorem exists_equilibrium' "$root/Econlib/Equilibrium/Existence.lean"
    grep -Fq 'WalrasianEquilibrium' "$root/Econlib/Equilibrium/Economy.lean"
    grep -Fq 'StationaryWalrasianEquilibrium' "$root/Econlib/Equilibrium/AggregateAccounting.lean"
    grep -Fq 'exists_stationary' "$root/Econlib/Probability/Markov/Ergodic.lean"
    grep -Fq 'theorem geometric_convergence_to' "$root/Econlib/Probability/Markov/Ergodic.lean"
    grep -Fq '0 < P.transition' "$root/Econlib/Probability/Markov/Ergodic.lean"

    grep -Fq 'BehavioralStrategy' "$root/Econlib/GameTheory/ExtensiveForm/Core/Strategy.lean"
    grep -Fq 'BeliefSystem' "$root/Econlib/GameTheory/ExtensiveForm/Refinements/BeliefSystem.lean"
    grep -Fq 'SequentialEquilibrium' "$root/Econlib/GameTheory/ExtensiveForm/Refinements/SequentialEquilibrium.lean"

    grep -Fq 'GeneralizedWalrasianData' "$local_theorem"
    grep -Fq 'GeneralizedWalrasianExistence' "$local_theorem"
    grep -Fq 'MegaGeneralizedWalrasianEquilibrium' "$local_theorem"
    grep -Fq 'CanonicalLearnerHodgeMaxwellCompositionTheorem' "$local_theorem"

    pomdp_named=false
    pomdp_named_dhall=False
    grep -Riq 'POMDP|partially observable' "$root/Econlib" && pomdp_named=true && pomdp_named_dhall=True || true

    mkdir -p .ci/discovery
    {
      printf '%s\n' '{'
      printf '  econlib_repo = "danlyng/Econlib",\n'
      printf '  econlib_commit = "%s",\n' "$econlib_rev"
      printf '  benchmark_regular_assumption = "Econlib::RegularEconomy",\n'
      printf '  benchmark_static_existence = "Econlib::Economy.exists_equilibrium",\n'
      printf '  non_iid_transition = "arbitrary Markov/kernel transition",\n'
      printf '  stationary_law_node = "FiniteMarkovChain.exists_stationary",\n'
      printf '  stationary_law_convergence_node = "FiniteMarkovChain.geometric_convergence_to",\n'
      printf '  stationary_law_convergence_condition = "strictly positive transition probabilities",\n'
      printf '  stationary_equilibrium_node = "MarkovExchangeEconomy.StationaryWalrasianEquilibrium",\n'
      printf '  local_mega_edge = "MegaGeneralizedWalrasianEquilibrium",\n'
      printf '  local_composition = "CanonicalLearnerHodgeMaxwellCompositionTheorem",\n'
      printf '  partial_observation_nodes = ["BehavioralStrategy", "BeliefSystem", "SequentialEquilibrium"],\n'
      printf '  pomdp_named_in_econlib = %s,\n' "$pomdp_named_dhall"
      printf '  composition_path = ["Econlib::RegularEconomy", "Econlib::Economy.exists_equilibrium", "Actions::MegaGeneralizedWalrasianEquilibrium", "Actions::CanonicalLearnerHodgeMaxwellCompositionTheorem"],\n'
      printf '  pomdp_bridge_status = "local POMDP belief-policy closure remains explicit; no filtering or optimality is inferred"\n'
      printf '%s\n' '}'
    } > .ci/discovery/econlib-equilibrium-graph.dhall

    dhall text --file .ci/discovery/econlib-equilibrium-graph.dhall >/dev/null
    grep -Fq 'benchmark_regular_assumption = "Econlib::RegularEconomy"' .ci/discovery/econlib-equilibrium-graph.dhall
    grep -Fq 'non_iid_transition = "arbitrary Markov/kernel transition"' .ci/discovery/econlib-equilibrium-graph.dhall
    grep -Fq 'pomdp_bridge_status = "local POMDP belief-policy closure remains explicit; no filtering or optimality is inferred"' .ci/discovery/econlib-equilibrium-graph.dhall
    echo "econlib-equilibrium-search=pass"
    echo "econlib-commit=$econlib_rev"
    echo "pomdp-named-in-upstream=$pomdp_named"
    '',
  StrictExistenceImpossibility = ''
    set -euo pipefail
    grep -Fq 'megaNoEquilibriumGeneralizedWalrasian' FullCoupled/TheoremsMonolith.agda
    grep -Fq 'noUnconditionalMegaGeneralizedWalrasianExistence' FullCoupled/TheoremsMonolith.agda
    echo 'strict-existence-impossibility-graph=source-inventory-only'
    '',  StationaryCycleImpossibility = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"

    theorem=FullCoupled/TheoremsMonolith.agda    ergodic="$tmp/Econlib/Econlib/Probability/Markov/Ergodic.lean"

    grep -Fq 'canonicalNoNontrivialFiniteCycle-theorem' "$theorem"
    grep -Fq 'canonicalNoFiniteStepConvergenceToFixedPoint' "$theorem"
    grep -Fq 'isomorphismNoFiniteCycleTransport' "$theorem"
    grep -Fq 'exists_stationary' "$ergodic"
    grep -Fq 'theorem geometric_convergence_to' "$ergodic"
    grep -Fq '0 < P.transition' "$ergodic"

    mkdir -p .ci/discovery
    cat > .ci/discovery/stationary-cycle-impossibility-graph.dhall <<'DHALL'
{
  rule = "FINITE_DETERMINISTIC_CYCLE_HAS_STATIONARY_WITNESS_BUT_IS_EXCLUDED",
  terminalStatus = "IMPOSSIBILITY",
  requiresExactFiniteDeterministicProjection = True,
  stationaryDistributionWitness = {
    type = "uniform_cycle_measure",
    statement = "For a deterministic cycle of length m>0, the uniform probability law on the cycle is stationary for the induced deterministic Markov kernel.",
    use = "witness_only"
  },
  upstreamStationaryLaw = {
    theorem = "Econlib::FiniteMarkovChain.exists_stationary",
    role = "independent finite-state existence fact; it does not imply that a cycle exists"
  },
  convergenceGuard = {
    theorem = "Econlib::FiniteMarkovChain.geometric_convergence_to",
    condition = "strictly positive transition probabilities",
    role = "separate conditional convergence result; not used to claim convergence of an arbitrary deterministic cycle"
  },
  nodes = [
    "Agda::finiteOrbit-collision",
    "deterministic finite recurrent cycle",
    "uniform cycle stationary law",
    "Econlib::FiniteMarkovChain.exists_stationary",
    "Econlib::FiniteMarkovChain.geometric_convergence_to",
    "Agda::canonicalNoNontrivialFiniteCycle-theorem",
    "Agda::canonicalNoFiniteStepConvergenceToFixedPoint"
  ],
  edges = [
    { source = "finiteOrbit-collision", target = "eventual periodic orbit", reason = None Text },
    { source = "eventual periodic orbit", target = "deterministic finite recurrent cycle", reason = None Text },
    { source = "deterministic finite recurrent cycle", target = "uniform cycle stationary law", reason = None Text },
    { source = "Econlib::FiniteMarkovChain.exists_stationary", target = "stationary distribution", reason = Some "independent existence witness" },
    { source = "Econlib::FiniteMarkovChain.geometric_convergence_to", target = "quantitative convergence", reason = Some "requires strict positivity" },
    { source = "deterministic finite recurrent cycle", target = "canonicalNoNontrivialFiniteCycle-theorem", reason = Some "contradiction" },
    { source = "period-1 recurrent cycle", target = "canonicalNoFiniteStepConvergenceToFixedPoint", reason = Some "contradiction" }
  ],
  logicGuard = "stationary-law existence is not itself an obstruction; the obstruction is the canonical no-cycle theorem",
  isomorphismTransportNode = "Agda::isomorphismNoFiniteCycleTransport",
  isomorphismTransportRole = "exact conjugacy preserves finite-cycle exclusion on the isomorphic state space",
  status = "strict graph: no third terminal status"
}
DHALL
    dhall text --file .ci/discovery/stationary-cycle-impossibility-graph.dhall >/dev/null
    grep -Fq 'terminalStatus = "IMPOSSIBILITY"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'stationaryDistributionWitness = {' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'type = "uniform_cycle_measure"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'logicGuard = "stationary-law existence is not itself an obstruction; the obstruction is the canonical no-cycle theorem"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'requiresExactFiniteDeterministicProjection = True' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'status = "strict graph: no third terminal status"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    ! grep -Eiq 'frontier|unknown|vague|unresolved|pending' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    echo "stationary-cycle-impossibility-graph=pass"
    '',
  IsomorphismTransport = ''
    set -euo pipefail
    grep -Fq 'isomorphismEqualityTransport' FullCoupled/TheoremsMonolith.agda
    grep -Fq 'isomorphismDisequalityTransport' FullCoupled/TheoremsMonolith.agda
    grep -Fq 'isomorphismIterateConjugacy' FullCoupled/TheoremsMonolith.agda
    grep -Fq 'isomorphismNoFiniteCycleTransport' FullCoupled/TheoremsMonolith.agda
    echo 'isomorphism-transport-closure=source-inventory-only'
    '',  SemanticContract = ''
    set -euo pipefail
    theorem=FullCoupled/TheoremsMonolith.agda
    learner=FullCoupled/CanonicalLearnerMonolith.agda
    nix run .#agda-import-sync -- --check
    required='
    canonical-recurrent-prefix-monoid-homomorphism
    canonicalF4-prefix-monoid-homomorphism
    
    canonicalGRUF4-prefix-monoid-homomorphism
    canonicalFullStep-GRUF4-prefix-bridge
    freeMonoidActionHomomorphism-from-square
    canonicalCount-freeMonoidActionHomomorphism
    canonicalNoNontrivialFiniteCycle-theorem
    StateIsomorphism
    canonicalDeterministicFiniteStepDivergenceInevitability
    canonicalNoFiniteStepConvergenceToFixedPoint
    CanonicalGlobalTokenEncodingConjugacyTheorem
    canonical-global-token-encoding-conjugacy
    CanonicalIntegerGRUTokenEncodingLeftInverse
    canonical-integer-gru-token-encoding-left-inverse
    canonicalIntegerGRUTokenEncodingInjective
    canonicalIntegerGRUTokenEncoding-continuous-discrete
    CanonicalIntegerGRUGlobalConjugateTheorem
    canonical-integer-gru-global-conjugate-theorem
    CanonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-lm-composition-theorem
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append
    CanonicalExactRNNLMTheorem
    canonical-exact-rnn-lm-theorem
    CanonicalIntegerHaarScaledOrthogonalityTheorem
    canonical-integer-haar-scaled-orthogonality-theorem
    CanonicalHaarRecurrentCompositionTheorem
    canonical-haar-recurrent-composition-theorem
    CanonicalLearnerPermutationCompositionImpossibilityTheorem
    canonical-learner-permutation-composition-impossibility-theorem
    CanonicalFullCompositionGraphTheorem
    canonical-full-composition-graph-theorem
    CanonicalAStarCostGuidanceTheorem
    CanonicalEndogenousEGraphAStarTransportClosureTheorem
    eGraphAStarConvergenceSemanticClosure
    eGraphAStarEventualStableFromRank
    eGraphAStarStablePathPersists
    eGraph-path-trans
    CanonicalIntegerLayerNormEGraphAStarTheorem
    integerLayerNorm-a-star-semantic-closure
    canonical-a-star-cost-guidance-theorem
    recurrentPrefix-scan-lifts-conjugacy
    canonical-recurrent-scan-conjugacy-theorem
    CanonicalFullLearnerConnectedScanConjugacyTheorem
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    CanonicalFiniteCycleExclusionIsomorphismTheorem
    CanonicalOperatorCompositionTheorem
    canonical-operator-composition-theorem
    CanonicalPureNonOrangeBypassCompletionTheorem
    CanonicalStationarySubcompositionTheorem
    ExactContractComputabilityBoundaryTheorem
    exact-contract-computability-boundary-theorem
    megaParetoOptimal
    MegaSecondWelfareTheoremBoundaryCounterexample
    megaSecondWelfareTheorem-boundary-counterexample
    megaNoStrictAffordableAlternative-is-demand-optimality
    nLabMaxwellEulerLagrangeShell-equivalence
    nLabMaxwellFourLawOneStepClosed
    nLabMaxwellIterateConjugacyClosed
    CanonicalGlobalTokenEncodingConjugacyTheorem
    CanonicalGlobalTokenLMCompositionTheorem
    
    CanonicalExactRNNLMTheorem
    canonicalLearnerBairdSevenStar
    canonicalGRUStatisticalEncodeLeftInverse
    leftInverse-implies-injective
    canonicalGRUStatisticalEncodeInjective
    JAXExecutionMirrorReproof
    jaxVmapAffine
    jaxAssociativePrefixSum
    jaxRecurrentScan
    jaxLexicographicScoreOrder
    jaxSparseSupportSize
    jaxSparseSupportTopK
    jaxSparsemaxPolicyIndex
    jaxIntegerLayerNormCenteredNumerators
    jaxIntegerLayerNormRadicand
    jaxBatchedIntegerLayerNormRadicand
    jaxSignedGate
    jaxGRUHiddenStep
    jaxBatchedGRUHiddenStep
    jaxTsallis2NearSparsityFraction
    jaxSupportSparsityFraction
    jaxJittedScanSum
    JAXExecutionMirrorReproof
    discreteExactUniversalUAPFromLeftInverse
    '
    while IFS= read -r symbol; do
      [ -z "$symbol" ] || grep -Fq "$symbol" "$theorem" || { echo "missing theorem symbol: $symbol"; exit 1; }
    done <<< "$required"
    [ ! -f .ci/discovery/learner_semantic_manifest.m ] || { echo "generated semantic lookup table present"; exit 1; }
    [ ! -f .ci/discovery/learner-semantic-laws.tsv ] || { echo "generated semantic law artifact present"; exit 1; }
    grep -Eiq 'walsh|rope|target-network|target_network|target network|normalization|regularization' "$learner" && { echo "forbidden semantic term present"; exit 1; } || true
    grep -Fq 'open import FullCoupled.CanonicalLearnerMonolith as C' "$theorem" || { echo "non-canonical theorem source"; exit 1; }
    grep -Fq 'neuralPolicyGreedyTwoEpsilonRegret' "$learner" || { echo "missing two-epsilon greedy regret theorem"; exit 1; }
    '',
  Surface = ''
    set -euo pipefail
    count=$(git ls-files '*Monolith.agda' | wc -l)
    [ "$count" -eq 2 ] || { echo "expected exactly two Agda monoliths, found $count"; exit 1; }
    agda_count=$(git ls-files '*.agda' | wc -l)
    [ "$agda_count" -eq 15 ] || { echo "expected exactly fifteen tracked Agda sources, found $agda_count"; exit 1; }
    [ -f FullCoupled/CanonicalLearnerMonolith.agda ] || { echo "missing canonical learner monolith"; exit 1; }
    [ -f FullCoupled/TheoremsMonolith.agda ] || { echo "missing theorem monolith"; exit 1; }
    imports=$(git ls-files '*.agda' | xargs grep -hE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+' || true)
    ! printf '%s\n' "$imports" | grep -E '(^|[[:space:]])(Fin|.*[.]Fin)([.]|[[:space:]]|$)|(^|[[:space:]])(Vec|.*[.]Vec)([.]|[[:space:]]|$)|(^|[[:space:]])Data[.]|(^|[[:space:]])Agda[.]Prelude([[:space:]]|$)' || { echo "forbidden Fin/Vec/stdlib/agda-prelude import present"; exit 1; }
    [ -f .ci/actions_ci.dhall ] || { echo "missing Dhall orchestrator"; exit 1; }
    ! git ls-files '*.json' | grep -q . || { echo "JSON source/artifact remains"; exit 1; }
    ! find .ci/discovery -type f -name '*.json' -print -quit | grep -q . || { echo "generated JSON artifact remains"; exit 1; }
    retired='evolutionary-search|evolutionary algorithm|sparsemax2pair|fixedtemperaturesparsemax|actionscore|policyleftweight|tsts|gresher'
    md_link_found=0
    while IFS= read -r md; do
      if grep -Eq '\\]\\(|https?://' "$md"; then
        echo "Markdown link found outside the Elm presentation: $md"
        md_link_found=1
      fi
    done < <(git ls-files '*.md' '*.markdown')
    [ "$md_link_found" -eq 0 ] || { echo "Markdown links are forbidden outside Elm sites"; exit 1; }
    ! git ls-files -z | xargs -0 grep -Eil "$retired" 2>/dev/null | grep -q . || { echo "retired semantic term present"; exit 1; }
    ! grep -nE '(^|[[:space:];])pkgs\.python3([[:space:]]|$)|(^|[[:space:];])python3([[:space:]]|$)|(^|[[:space:];])python([[:space:]]|$)|pkgs\.pythonPackages' flake.nix .ci/*.sh .ci/*.dhall .ci/lua/*.fnl 2>/dev/null || { echo "non-JAX Python toolchain reference present"; exit 1; }
    ! grep -nE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+(MLTT\\.Fin|Data\\.Fin|Fin\\.Base|Data\\.Vec|Vec\\.Base)([[:space:]]|$)' -- *.agda FullCoupled/**/*.agda 2>/dev/null || { echo "Fin/Vec imports are forbidden; use Nat/List/Set instead"; exit 1; }
    # Canonical proof/data surface: use Nat, Int/Integer, Rational, List, and Set-like structures.
    # Keep Fin and Vec out of the project-owned Agda API; transitive library internals remain library concerns.
    ! git ls-files '*.agda' -z | xargs -0 grep -nE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+((Fin|Vec)(\.|[[:space:]]|$)|[^[:space:]]+\.(Fin|Vec)(\.|[[:space:]]|$))' 2>/dev/null || { echo "Fin/Vec import introduced into project Agda sources"; exit 1; }
    ! grep -nE 'Exotic/ERL/FullCoupled|Exotic/FullCoupled' FullCoupled/*.agda README.md site/Main.elm docs/*.md 2>/dev/null || { echo "stale Exotic source path present"; exit 1; }
    '',
  Versions = ''
    set -euo pipefail
    ghc --numeric-version
    test -n "$(ghc --numeric-version)"
    "$AGDA_COMMAND" --version
    nix run .#fennel-smoke
    dhall --version
    z3 --version
    emacs --version
    emacs --batch --eval '(require (quote agda2-mode))'
    '',
  AutoMerge = ''
    set -euo pipefail
    : "''${GH_TOKEN:?GH_TOKEN is required}"
    : "''${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required}"
    : "''${PR_NUMBER:?PR_NUMBER is required}"
    label_present="$(gh pr view "$PR_NUMBER" --repo "$GITHUB_REPOSITORY" --json labels --jq '.labels | any(.[]; .name == "auto-merge-approved")')"
    if [[ "$label_present" != "true" ]]; then
      echo "auto-merge=skipped (requires the explicit auto-merge-approved label)"
      exit 0
    fi
    gh pr merge "$PR_NUMBER" --repo "$GITHUB_REPOSITORY" --auto --rebase
    '',
  All = ''
    set -euo pipefail
    nix run .#fennel-smoke
    "$AGDA_COMMAND" --version
    ghc --numeric-version
    dhall --version
    emacs --version
    emacs --batch --eval '(require (quote agda2-mode))'
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSurface.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSemanticExtractor.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsTheoremGraphEGraph.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsSemanticSearch.agda
    "$AGDA_COMMAND" -i . FullCoupled/Agda2HsGraphSearchCheck.agda
    nix run .#agda2hs-graph-search-check
    nix run .#scott-strachey-domain-check
    nix run .#monoid-lstm-stream-check
    nix run .#agda2hs-semantic-search
    echo 'agda-all=pass'
  ''} lane

in policyGate ++ "\n" ++ script
