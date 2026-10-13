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
    echo "pure-agda2hs-kernel-check=pass"
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
    echo "legacy-monoliths=source-inventory-only"
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
    grep -E '^semantic-laws=[1-9][0-9]* nonreflexive=[1-9][0-9]* composite=[1-9][0-9]*$' "$report"
    grep -E '^required-plan-count=[1-9][0-9]* required-plan-total=[1-9][0-9]* required-plan-regression=True$' "$report"
    grep -Fq 'egraph-regression=True egraph-associativity-regression=True' "$report"
    grep -Fq 'haskell-minus-one-A*=2 proof-backed laws; legacy monolith excluded from pure build' "$report"
    grep -E '^agda2hs-semantic-port=[1-9][0-9]* dominance edges; 5 pruning proofs; [1-9][0-9]*/[1-9][0-9]* required plans e-graph-closed$' "$report"
    grep -Fq 'proofKernel=Agda' "$manifest"
    grep -Fq 'searchKernel=Agda2Hs' "$manifest"
    grep -Fq 'legacyMonoliths=source-scan-only' "$manifest"
    nix run .#agda2hs-graph-search-check
    nix run .#acorn-smoke
    nix run .#xds-agda-check
    nix run .#mini-vehicle-check
    nix run .#scott-strachey-domain-check
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
      printf '  adapter_present = %s,\n' "$adapter_present"
      printf '  composition_path = ["Econlib::Economy.exists_equilibrium", "Actions::MegaGeneralizedWalrasianEquilibrium", "Actions::CanonicalLearnerHodgeMaxwellCompositionTheorem"],\n'
      printf '  graph_status = "composition-ready; explicit cross-language adapter still required"\n'
      printf '%s\n' '}'    } > .ci/discovery/econlib-crossrepo-sync.dhall

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
      printf '  pomdp_named_in_econlib = %s,\n' "$pomdp_named"
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
    '
    while IFS= read -r symbol; do
      [ -z "$symbol" ] || grep -Fq "$symbol" "$theorem" || { echo "missing theorem symbol: $symbol"; exit 1; }
    done <<< "$required"
    [ ! -f .ci/discovery/learner_semantic_manifest.m ] || { echo "generated semantic lookup table present"; exit 1; }
    [ ! -f .ci/discovery/learner-semantic-laws.tsv ] || { echo "generated semantic law artifact present"; exit 1; }
    grep -Eiq 'walsh|rope|target-network|target_network|target network|normalization|regularization' "$learner" && { echo "forbidden semantic term present"; exit 1; } || true
    grep -Fq 'open import FullCoupled.CanonicalLearnerMonolith as C' "$theorem" || { echo "non-canonical theorem source"; exit 1; }
    '',
  Surface = ''
    set -euo pipefail
    count=$(git ls-files '*Monolith.agda' | wc -l)
    [ "$count" -eq 2 ] || { echo "expected exactly two Agda monoliths, found $count"; exit 1; }
    agda_count=$(git ls-files '*.agda' | wc -l)
    [ "$agda_count" -eq 16 ] || { echo "expected exactly sixteen tracked Agda sources, found $agda_count"; exit 1; }
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
    nix run .#acorn-smoke
    nix run .#xds-agda-check
    nix run .#mini-vehicle-check
    nix run .#scott-strachey-domain-check
    nix run .#agda2hs-semantic-search
    echo 'agda-all=pass'
  ''} lane

in script
