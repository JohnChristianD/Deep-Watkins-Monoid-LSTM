{
  description = "Agda2HS graph search with the unmodified Nixpkgs Agda2HS toolchain and Lua/Luafun support";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0439f75413ace6c42e4c722cafd4d6e5401de648";
    luafun = {
      url = "github:luafun/luafun/02960048e4dff4f5fd5b683c4b61f9df42e8339f";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    luafun
  }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;

      pkgsFor = system:
        import nixpkgs {
          inherit system;
        };

      agda2hsTool = system:
        (pkgsFor system).haskellPackages.agda2hs;

      # The pinned defaultShowList combines Agda 2.8's unresolved level and
      # instance metas in a higher-order fold. Use the definitionally equivalent
      # recursive renderer: keep the class signatures and ordinary output intact.
      agda2hsBaseLib = system:
        let
          pkgs = pkgsFor system;
          upstream = pkgs.agdaPackages.agda2hs-base;
        in
        (pkgs.runCommand "agda2hs-base-show-universe-compat" {
          nativeBuildInputs = [ pkgs.python3 ];
        } ''
          mkdir -p "$out"
          cp -RL "${upstream}/." "$out/"
          chmod -R u+w "$out"
          show_source="$(find "$out" -path '*/Haskell/Prim/Show.agda' -print -quit)"
          test -n "$show_source" || {
            echo "Haskell/Prim/Show.agda not found in pinned agda2hs-base" >&2
            exit 1
          }
          grep -Fq 'record Show₁ (a : Type) : Type where' "$show_source"
          grep -Fq 'record Show₂ (a : Type) : Type where' "$show_source"
          python - "$show_source" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_text()
old = """defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList shows = λ where
  []       → showString "[]"
  (x ∷ xs) → showString "["
           ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs
           ∘ showString "]"
"""
new = """defaultShowListTail : {@0 a : Type} → (a → ShowS) → List a → ShowS
defaultShowListTail {a = a} shows [] = showString "]"
defaultShowListTail {a = a} shows (x ∷ xs) =
  showChar ',' ∘ shows x ∘ defaultShowListTail {a = a} shows xs

defaultShowList : {@0 a : Type} → (a → ShowS) → List a → ShowS
defaultShowList {a = a} shows [] = showString "[]"
defaultShowList {a = a} shows (x ∷ xs) =
  showString "[" ∘ shows x ∘ defaultShowListTail {a = a} shows xs
"""
if old not in source:
    raise SystemExit("pinned Haskell.Prim.Show defaultShowList block changed; refusing a fuzzy edit")
path.write_text(source.replace(old, new, 1))
PY
          grep -Fq 'defaultShowListTail {a = a} shows (x ∷ xs)' "$show_source"
          grep -Fq "showChar ','" "$show_source"
          grep -Fq 'defaultShowList {a = a} shows (x ∷ xs)' "$show_source"
          find "$out" -name '*.agda-lib' -print -quit | grep -q .
        '') // {
          # Nix's Agda package-set builder requires this metadata when building
          # its libraries file. Preserve the pinned upstream package contract.
          inherit (upstream) libraryFile;
        };

      agdaEmacs = system:
        let
          pkgs = pkgsFor system;
        in
        (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (epkgs: [
          epkgs.agda2-mode
        ]);

      # Keep only the two consumer-side GHC extensions required by this project.
      ghcLanguageFlags = [
        "-XMonoLocalBinds"
        "-XNoMonomorphismRestriction"
      ];

      canonicalGhc = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.haskellPackages.ghcWithPackages (p: [
          p.liquidhaskell
        ]);

      agdaWithPackages = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agda.withPackages {
          pkgs = [
            (agda2hsBaseLib system)
          ];
          ghc = null;
        };

      agdaWithStandardLibrary = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agda.withPackages {
          pkgs = [ pkgs.agdaPackages.standard-library ];
          ghc = null;
        };

      agda2hsWithCanonicalGhc = system:
        agda2hsTool system;


      luafunModule = system:
        let
          pkgs = pkgsFor system;
          lua = pkgs.luajit;
        in
        pkgs.luajitPackages.buildLuaPackage {
          pname = "luafun";
          version = "scm-1";
          src = luafun;
          dontBuild = true;
          installPhase = ''
            runHook preInstall
            install -Dm0644 fun.lua "$out/share/lua/${lua.luaversion}/fun.lua"
            runHook postInstall
          '';
          meta = {
            description = "High-performance functional programming library for Lua";
            homepage = "https://luafun.github.io/";
            license = pkgs.lib.licenses.mit;
          };
        };

      luaFennelEnv = system:
        let
          pkgs = pkgsFor system;
          luafunPkg = luafunModule system;
        in
        pkgs.luajit.withPackages (ps: [
          ps.fennel
          luafunPkg
        ]);

      fennelRuntime = system:
        let
          pkgs = pkgsFor system;
          luaEnv = luaFennelEnv system;
        in
        pkgs.writeShellApplication {
          name = "fennel";
          runtimeInputs = [ luaEnv ];
          text = ''
            exec ${luaEnv}/bin/fennel "$@"
          '';
        };

      streamlyGhc = system:
        let pkgs = pkgsFor system;
        in
        pkgs.haskellPackages.ghcWithPackages (p: [
          p.streamly
          p.streamly-bytestring
          p.streamly-core
        ]);

      agdaCli = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda";
          runtimeInputs = [
            (agdaWithPackages system)
            pkgs.coreutils
            pkgs.findutils
          ];
          text = ''
            mapfile -t agda_global_options < "${./.ci/agda/global-options.txt}"
            agda2hs_base_lib="$(find "${agda2hsBaseLib system}" -name '*.agda-lib' -print -quit)"
            if [[ -z "$agda2hs_base_lib" ]]; then
              echo "agda2hs-base .agda-lib not found in Nix package" >&2
              exit 1
            fi
            agda2hs_base_root="$(dirname "$agda2hs_base_lib")"
            agda2hs_base_work="$(mktemp -d)"
            trap 'rm -rf "$agda2hs_base_work"' EXIT
            mkdir -p "$agda2hs_base_work/library"
            cp -RL "$agda2hs_base_root/." "$agda2hs_base_work/library/"
            chmod -R u+rwX "$agda2hs_base_work/library"
            if "${agdaWithPackages system}/bin/agda" "''${agda_global_options[@]}" -i "$agda2hs_base_work/library" -i . "$@"; then
              status=0
            else
              status=$?
            fi
            exit "$status"
          '' ;
        };

      agdaCommand = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda2hs-agda";
          runtimeInputs = [
            (agdaWithPackages system)
            pkgs.coreutils
            pkgs.findutils
          ];
          text = ''
            mapfile -t agda_global_options < "${./.ci/agda/global-options.txt}"
            agda2hs_base_lib="$(find "${agda2hsBaseLib system}" -name '*.agda-lib' -print -quit)"
            if [[ -z "$agda2hs_base_lib" ]]; then
              echo "agda2hs-base .agda-lib not found in Nix package" >&2
              exit 1
            fi
            agda2hs_base_root="$(dirname "$agda2hs_base_lib")"
            agda2hs_base_work="$(mktemp -d)"
            trap 'rm -rf "$agda2hs_base_work"' EXIT
            mkdir -p "$agda2hs_base_work/library"
            cp -RL "$agda2hs_base_root/." "$agda2hs_base_work/library/"
            chmod -R u+rwX "$agda2hs_base_work/library"
            if agda "''${agda_global_options[@]}" -i "$agda2hs_base_work/library" -i . "$@"; then
              status=0
            else
              status=$?
            fi
            exit "$status"
          '' ;
        };

      agda2hsCommand = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda2hs-ci";
          runtimeInputs = [
            (agda2hsWithCanonicalGhc system)
            (agdaWithPackages system)
            pkgs.coreutils
            pkgs.findutils
          ];
          text = ''
            mapfile -t agda_global_options < "${./.ci/agda/global-options.txt}"
            agda2hs_base_lib="$(find "${agda2hsBaseLib system}" -name '*.agda-lib' -print -quit)"
            if [[ -z "$agda2hs_base_lib" ]]; then
              echo "agda2hs-base .agda-lib not found in Nix package" >&2
              exit 1
            fi
            agda2hs_base_root="$(dirname "$agda2hs_base_lib")"
            agda2hs_base_work="$(mktemp -d)"
            trap 'rm -rf "$agda2hs_base_work"' EXIT
            mkdir -p "$agda2hs_base_work/library"
            cp -RL "$agda2hs_base_root/." "$agda2hs_base_work/library/"
            chmod -R u+rwX "$agda2hs_base_work/library"
            if agda2hs "''${agda_global_options[@]}" --config "${./.ci/agda/agda2hs.yaml}" -i "$agda2hs_base_work/library" -i . "$@"; then
              status=0
            else
              status=$?
            fi
            exit "$status"
          '' ;
        };
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          agda = agdaCli system;
          agda2hs = agda2hsWithCanonicalGhc system;
          agda-emacs = agdaEmacs system;
          agda2hs-graph-search-check = let
            script = pkgs.writeShellApplication {
              name = "agda2hs-graph-search-check";
              runtimeInputs = [
                (agdaCli system)
                (agda2hsCommand system)
                (canonicalGhc system)
                pkgs.coreutils
                pkgs.gnugrep
              ];
              text = ''
                set -euo pipefail
                out="build/agda2hs-graph-search-check"
                rm -rf "$out"
                mkdir -p "$out"

                # Non-graph-search theorem work belongs in the two monoliths.
                # This target proves only the graph/e-graph search contract.

                # This lane checks only the Agda2HS runtime module closure.
                # Historical theorem monoliths are outside this kernel-checked target.
                for source in \
                  FullCoupled/CanonicalLearnerMonolith.agda \
                  FullCoupled/TheoremsMonolith.agda \
                  FullCoupled/Agda2HsSemanticExtractor.agda \
                  FullCoupled/Agda2HsTheoremGraphEGraph.agda \
                  FullCoupled/Agda2HsSemanticSearch.agda; do
                  if grep -Eq '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Agda\.Builtin\.(Nat|Equality|List)([[:space:]]|$)' "$source"; then
                    echo "Agda2HS runtime module bypasses Haskell.Prelude: $source" >&2
                    exit 1
                  fi
                done
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsSemanticExtractor.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsSemanticSearch.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsGraphSearchCheck.agda

                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSemanticExtractor.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsTheoremGraphEGraph.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSemanticSearch.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsGraphSearchCheck.agda -o "$out"

                test -s "$out/FullCoupled/Agda2HsSemanticExtractor.hs"
                test -s "$out/FullCoupled/Agda2HsTheoremGraphEGraph.hs"
                test -s "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                test -s "$out/FullCoupled/Agda2HsGraphSearchCheck.hs"

                mkdir -p "$out/ghc"
                "${canonicalGhc system}/bin/ghc" \
                  -O0 \
                  -dcore-lint \
                                    -i"$out" \
                  -odir "$out/ghc" \
                  -hidir "$out/ghc" \
                  -main-is FullCoupled.Agda2HsGraphSearchCheck.main \
                  -o "$out/graph-search-check" \
                  "$out/FullCoupled/Agda2HsGraphSearchCheck.hs"

                "$out/graph-search-check" > "$out/report.txt"
                grep -Fxq "graph-two-leaf-branches=True" "$out/report.txt"
                grep -Fxq "graph-dependency-order=True" "$out/report.txt"
                grep -Fxq "graph-best-first-tie=True" "$out/report.txt"
                grep -Fxq "graph-best-g-policy=True" "$out/report.txt"
                grep -Fxq "graph-admissible-heuristic=True" "$out/report.txt"
                grep -Fxq "graph-cycle-rejected=True" "$out/report.txt"
                grep -Fxq "graph-closure-duplicate-dependencies=True" "$out/report.txt"
                grep -Fxq "graph-duplicate-edge-normalization=True" "$out/report.txt"
                grep -Fxq "graph-multi-parent-dag=True" "$out/report.txt"
                grep -Fxq "graph-self-loop-rejected=True" "$out/report.txt"
                grep -Fxq "graph-dot-parser-regression=True" "$out/report.txt"
                grep -Fxq "graph-linear-chain=True" "$out/report.txt"
                grep -Fxq "graph-search-contract=True" "$out/report.txt"
                grep -Fxq "canonical-search-egraph-closed=True" "$out/report.txt"
                grep -Fxq "graph-astar-egraph-closed=True" "$out/report.txt"

                compiler_version=$("${canonicalGhc system}/bin/ghc" --numeric-version)
                printf '%s\n' \
                  "compiler=ghc-$compiler_version" \
                  "proofKernel=Agda" \
                  "searchKernel=Agda2Hs" \
                  "legacyMonoliths=source-scan-only" \
                  "theoremMonolith=not-loaded" \
                  "graphSearchContract=pass" \
                  > "$out/manifest.tsv"
                cat "$out/manifest.tsv"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda2hs-graph-search-check";
          };

          agda2hs-semantic-search = let
            script = pkgs.writeShellApplication {
              name = "agda2hs-semantic-search";
              runtimeInputs = [
                (agdaCommand system)
                (agda2hsCommand system)
                pkgs.haskellPackages.liquidhaskell
                pkgs.z3
                pkgs.coreutils
                pkgs.git
              ];
              text = ''
                set -euo pipefail
                out="build/agda2hs-semantic-search"
                rm -rf "$out"
                mkdir -p "$out"
                "${agdaCommand system}/bin/agda2hs-agda" --dependency-graph="$out/semantic-search.dot" -i . FullCoupled/Agda2HsSemanticSearch.agda
                test -s "$out/semantic-search.dot"
                bash .ci/discovery/agda_semantic_source_closure.sh \
                  "$out/semantic-search.dot" \
                  "$out/.semantic-source-files" \
                  "$PWD/FullCoupled/Agda2HsSemanticSearch.agda" \
                  "${agda2hsBaseLib system}"
                test -s "$out/.semantic-source-files"
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsSemanticExtractor.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsSemanticSearch.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSemanticExtractor.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSemanticSearch.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsTheoremGraphEGraph.agda -o "$out"
                test -s "$out/FullCoupled/Agda2HsSemanticExtractor.hs"
                test -s "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                test -s "$out/FullCoupled/Agda2HsTheoremGraphEGraph.hs"
                grep -Fq "symbolicEGraphRegression" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "eGraphAssociativityRegression" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "canonicalBindingsRegression" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "hashconsAfterUnionRegression" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "requiredTheoremNames" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "requiredPlanComplete" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "inverse-correct" FullCoupled/TheoremsMonolith.agda
                grep -Fq "inverse-csearchable" FullCoupled/TheoremsMonolith.agda
                grep -Fq "inverse-preserves-csearchability" FullCoupled/TheoremsMonolith.agda
                grep -Fq "SearchableEquivalence" FullCoupled/TheoremsMonolith.agda
                mkdir -p "$out/ghc"
                "${canonicalGhc system}/bin/ghc" \
                  -O0 \
                  -dcore-lint \
                                    -i"$out" \
                  -odir "$out/ghc" \
                  -hidir "$out/ghc" \
                  -main-is FullCoupled.Agda2HsSemanticSearch.main \
                  -o "$out/agda2hs-semantic-search" \
                  "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                "$out/agda2hs-semantic-search" > "$out/report.txt"
                cat "$out/report.txt"
                grep -Fq "True" "$out/report.txt"
                grep -E '^theorem-graph-edges=[1-9][0-9]* autonomous-depth-first-chains=[1-9][0-9]*$' "$out/report.txt"
                grep -E '^agda2hs autonomous theorem-graph DFS: [1-9][0-9]* maximal dependency chains$' "$out/report.txt"
                grep -Fq "autonomous-regression=True" "$out/report.txt"
                grep -Fq "graph-branch-regression=True" "$out/report.txt"
                grep -Fq "graph-two-leaf-paths=True" "$out/report.txt"
                grep -Fq "graph-cycle-rejected=True" "$out/report.txt"
                grep -Fq "graph-path-count-dp=True" "$out/report.txt"
                grep -E "^semantic-laws=[1-9][0-9]* nonreflexive=[1-9][0-9]* composite=[1-9][0-9]*$" "$out/report.txt"
                if ! grep -E "^required-plan-count=[1-9][0-9]* required-plan-total=[1-9][0-9]* required-plan-regression=True$" "$out/report.txt"; then
                  echo "required theorem graph closure failed; observed plans:" >&2
                  grep -E '^required-plan-|learner-static-graph|learner-semantic-bridge' "$out/report.txt" >&2 || true
                  exit 1
                fi
                grep -Fq "learner-semantic-bridge-closure=True" "$out/report.txt"
                grep -Fq "semantic-identifier-normalization=True" "$out/report.txt"
                grep -Fq "source-only-legacy-boundary=True" "$out/report.txt"
                grep -Fq "graphTwoLeafBranchesRegression" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "egraph-regression=True egraph-associativity-regression=True" "$out/report.txt"
                grep -Fq "egraph-canonical-bindings=True" "$out/report.txt"
                grep -Fq "egraph-hashcons-after-union=True" "$out/report.txt"
                grep -Fq "egraph-constructivist-postulates=True" "$out/report.txt"
                grep -Fq "scottErshovNLabDenotationalSemanticsRegression" FullCoupled/TheoremsMonolith.agda
                grep -Fq "canonicalLearnerTraceDenotationStep" FullCoupled/TheoremsMonolith.agda
                grep -Fq "russianConstructivismPostulateRule" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "scottErshovDenotationalSemanticsPostulateRule" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "bishopConstructivismPostulateRule" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                grep -Fq "canonical-search-egraph-closed=True" "$out/report.txt"
                grep -Fq "graph-astar-egraph-closed=True" "$out/report.txt"
                compiler_version=$("${canonicalGhc system}/bin/ghc" --numeric-version)
                printf '%s\n' \
                  "compiler=ghc-$compiler_version" \
                  "plugins=none" \
                  "proofKernel=Agda" \
                  "searchKernel=Agda2Hs" \
                  "legacyMonoliths=source-scan-only" \
                  "semanticCompletenessCheck=pass" \
                  "nontrivialCheck=pass" \
                  > "$out/agda2hs-semantic-search-manifest.tsv"
                cat "$out/agda2hs-semantic-search-manifest.tsv"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda2hs-semantic-search";
          };

          agda2hs-extract = let
            script = pkgs.writeShellApplication {
              name = "agda2hs-extract";
              runtimeInputs = [
                (agda2hsCommand system)
                pkgs.coreutils
              ];
              text = ''
                set -euo pipefail
                out="build/agda2hs"
                rm -rf "$out"
                mkdir -p "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSurface.agda -o "$out"
                test -s "$out/FullCoupled/Agda2HsSurface.hs"
                echo "agda2hs-extract=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda2hs-extract";
          };

          agda-haskell-pipeline = let
            script = pkgs.writeShellApplication {
              name = "agda-haskell-pipeline";
              runtimeInputs = [
                (agdaCommand system)
                (agda2hsCommand system)
                pkgs.haskellPackages.liquidhaskell
                pkgs.z3
                pkgs.coreutils
                pkgs.findutils
                pkgs.git
                pkgs.stdenv.cc
              ];
              text = ''
                set -euo pipefail
                out="build/agda-haskell"
                rm -rf "$out"
                mkdir -p "$out"
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsSurface.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsSemanticExtractor.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsTheoremGraphEGraph.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsSemanticSearch.agda
                "${agdaCommand system}/bin/agda2hs-agda" FullCoupled/Agda2HsGraphSearchCheck.agda
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSurface.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSemanticExtractor.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsTheoremGraphEGraph.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSemanticSearch.agda -o "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsGraphSearchCheck.agda -o "$out"
                test -s "$out/FullCoupled/Agda2HsSurface.hs"
                test -s "$out/FullCoupled/Agda2HsSemanticExtractor.hs"
                test -s "$out/FullCoupled/Agda2HsTheoremGraphEGraph.hs"
                test -s "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                test -s "$out/FullCoupled/Agda2HsGraphSearchCheck.hs"
                mkdir -p "$out/ghc"
                "${canonicalGhc system}/bin/ghc" ${builtins.concatStringsSep " " ghcLanguageFlags} -O0 -dcore-lint -i"$out" -odir "$out/ghc" -hidir "$out/ghc" -c "$out/FullCoupled/Agda2HsSurface.hs"
                mkdir -p "$out/ghc-search"
                "${canonicalGhc system}/bin/ghc" \
                  -O0 -dcore-lint -i"$out" \
                  -odir "$out/ghc-search" -hidir "$out/ghc-search" \
                  -main-is FullCoupled.Agda2HsGraphSearchCheck.main \
                  -o "$out/graph-search-check" \
                  "$out/FullCoupled/Agda2HsGraphSearchCheck.hs"
                "$out/graph-search-check" > "$out/graph-search-report.txt"
                grep -Fxq "graph-two-leaf-branches=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-dependency-order=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-best-first-tie=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-best-g-policy=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-cycle-rejected=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-linear-chain=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-search-contract=True" "$out/graph-search-report.txt"
                liquid --version
                z3 --version
                compiler_version=$("${canonicalGhc system}/bin/ghc" --numeric-version)
                printf '%s\n' \
                  "compiler=ghc-$compiler_version" \
                  "readableModules=5" \
                  "proofKernel=Agda" \
                  "searchKernel=Agda2Hs" \
                  "legacyMonoliths=source-scan-only" \
                  "graphSearchContract=pass" \
                  > "$out/agda2hs-manifest.tsv"
                cat "$out/agda2hs-manifest.tsv"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda-haskell-pipeline";
          };

          default = {
            type = "app";
            program = "${pkgs.dhall}/bin/dhall";
          };
        });

      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          presentation = pkgs.mkShell {
            packages = [
              (fennelRuntime system)
              pkgs.luajit
              pkgs.stdenv.cc
              pkgs.coreutils
              pkgs.findutils
              pkgs.gawk
              pkgs.git
              pkgs.gnugrep
              pkgs.gnused
              pkgs.elmPackages.elm
              pkgs.dhall
              pkgs.dhall-json
            ];
          };

          agda-emacs = pkgs.mkShell {
            packages = [
              (agdaCli system)
              (agdaCommand system)
              (agdaEmacs system)
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };

          simple-haskell = pkgs.mkShell {
            packages = [
              (canonicalGhc system)
              pkgs.z3
            ];
            shellHook = ''
            '';
          };

          streamly = pkgs.mkShell {
            packages = [
              (streamlyGhc system)
              pkgs.haskellPackages.cabal-install
            ];
          };

          agda-ci = pkgs.mkShellNoCC {
            packages = [
              pkgs.dhall
              (agdaCommand system)
              pkgs.z3
              pkgs.coreutils
              pkgs.findutils
              pkgs.git
              pkgs.gawk
              pkgs.gnugrep
              pkgs.gnused
            ];
            shellHook = ''
              set -euo pipefail
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };

          agda-versions = pkgs.mkShellNoCC {
            packages = [
              (canonicalGhc system)
              pkgs.dhall
              pkgs.z3
              (agdaCommand system)
              (agdaEmacs system)
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };

          ci = pkgs.mkShell {
            packages = [
              pkgs.dhall
              (agdaCommand system)
              pkgs.z3
              pkgs.coreutils
              pkgs.findutils
              pkgs.git
              pkgs.gh
              pkgs.gnugrep
              pkgs.gnused
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };

          default-versions = pkgs.mkShell {
            packages = [
              (canonicalGhc system)
              pkgs.dhall
              pkgs.z3
              pkgs.gh
              (agdaCommand system)
              (agdaEmacs system)
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };

          default = pkgs.mkShell {
            packages = [
              pkgs.dhall
              (canonicalGhc system)
              pkgs.haskellPackages.cabal-install
              pkgs.z3
              pkgs.dhall-json
              pkgs.gh
              (agdaCommand system)
              (agdaEmacs system)
              pkgs.stdenv.cc
              pkgs.elmPackages.elm
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };
        });
    };
}