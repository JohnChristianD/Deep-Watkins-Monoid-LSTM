{
  description = "Pinned Nix environment for the Agda kernel, typed semantic search, and Dhall CI scripting";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0439f75413ace6c42e4c722cafd4d6e5401de648";
    typetopology = {
      url = "github:martinescardo/TypeTopology/8761920fdaec20c9dada7ff1d6628c09491245c5";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    typetopology
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

      agda2hsBaseLib = system:
        (pkgsFor system).agdaPackages.agda2hs-base;

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
          p.rio
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

      agda2hsWithCanonicalGhc = system:
        agda2hsTool system;

      agdaTypeTopologySetup = ''
        set -euo pipefail
        typetopology_dir="''${TMPDIR:-/tmp}/agda2hs-typetopology"
        if [ ! -f "$typetopology_dir/.ready" ]; then
          rm -rf "$typetopology_dir"
          mkdir -p "$typetopology_dir"
          cp -a "${typetopology}/source" "$typetopology_dir/source"
          cp "${typetopology}/typetopology.agda-lib" "$typetopology_dir/"
          touch "$typetopology_dir/.ready"
        fi
      '' ;

      agdaProofCommand = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda-proof";
          runtimeInputs = [
            pkgs.agda
            pkgs.coreutils
          ];
          text = ''
            ${agdaTypeTopologySetup}
            exec agda -i "$typetopology_dir/source" -i . "$@"
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
          ];
          text = ''
            exec agda -l agda2hs-base -i . "$@"
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
            pkgs.coreutils
          ];
          text = ''
            exec agda2hs -l agda2hs-base -i . "$@"
          '' ;
        };
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          agda = agdaWithPackages system;
          agda2hs = agda2hsWithCanonicalGhc system;
          ci = pkgs.dhall;
          default = pkgs.dhall;
        });

      apps = forAllSystems (system:
        let
          pkgs = pkgsFor system;
        in
        {
          ci = {
            type = "app";
            program = "${pkgs.dhall}/bin/dhall";
          };
          mirth-fast-dirty-source = let
            script = pkgs.writeShellApplication {
              name = "mirth-fast-dirty-source";
              runtimeInputs = [ pkgs.coreutils ];
              text = ''
                set -euo pipefail
                cat .ci/mirth/agda_to_elm.mth
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-fast-dirty-source";
          };
          mirth-c99-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-c99-sync";
              runtimeInputs = [ pkgs.mirth pkgs.stdenv.cc pkgs.coreutils ];
              text = ''
                set -euo pipefail
                test "$#" = 1
                output="$1"
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                mirthc .ci/mirth/agda_to_elm.mth -o "$tmp/agda-to-elm.c"
                cc -std=c99 "$tmp/agda-to-elm.c" -o "$output"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-c99-sync";
          };
          mirth-agda-import-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-import-sync";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_import_sync.sh "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-import-sync";
          };

          mirth-agda-command-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-command-sync";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_command_sync.sh "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-command-sync";
          };

          mirth-agda-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-sync";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_import_sync.sh "$@"
                bash .ci/mirth/agda_command_sync.sh "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-sync";
          };

          mirth-ascii-sync = let
            script = pkgs.writeShellApplication {
              name = "mirth-ascii-sync";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/ascii_surface.sh
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-ascii-sync";
          };

          mirth-agda-graph = let
            script = pkgs.writeShellApplication {
              name = "mirth-agda-graph";
              runtimeInputs = [ pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                bash .ci/mirth/agda_graph.sh "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mirth-agda-graph";
          };
          agda2hs-graph-search-check = let
            script = pkgs.writeShellApplication {
              name = "agda2hs-graph-search-check";
              runtimeInputs = [
                (agdaCommand system)
                (agda2hsCommand system)
                (canonicalGhc system)
                pkgs.coreutils
              ];
              text = ''
                set -euo pipefail
                out="build/agda2hs-graph-search-check"
                rm -rf "$out"
                mkdir -p "$out"

                # This lane checks only the Agda2HS runtime module closure.
                # It intentionally avoids agda-proof and TheoremsMonolith.
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

                "${canonicalGhc system}/bin/ghc" \
                  -O0 \
                  -dcore-lint \
                  -i "$out" \
                  -odir "$out/ghc" \
                  -hidir "$out/ghc" \
                  -main-is FullCoupled.Agda2HsGraphSearchCheck.main \
                  -o "$out/graph-search-check" \
                  "$out/FullCoupled/Agda2HsGraphSearchCheck.hs"

                "$out/graph-search-check" > "$out/report.txt"
                grep -Fxq "graph-two-leaf-branches=True" "$out/report.txt"
                grep -Fxq "graph-dependency-order=True" "$out/report.txt"
                grep -Fxq "graph-best-first-tie=True" "$out/report.txt"
                grep -Fxq "graph-cycle-policy=True" "$out/report.txt"
                grep -Fxq "graph-linear-chain=True" "$out/report.txt"
                grep -Fxq "graph-search-contract=True" "$out/report.txt"

                compiler_version=$("${canonicalGhc system}/bin/ghc" --numeric-version)
                printf '%s\n' \
                  "compiler=ghc-$compiler_version" \
                  "proofKernel=Agda" \
                  "searchKernel=Agda2Hs" \
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
                (agdaProofCommand system)
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
                bash .ci/mirth/agda_command_sync.sh --check
                "${agdaProofCommand system}/bin/agda-proof" --dependency-graph="$out/theorems-monolith.dot" -i . FullCoupled/TheoremsMonolith.agda
                test -s "$out/theorems-monolith.dot"
                bash .ci/discovery/agda_semantic_source_closure.sh \
                  "$out/theorems-monolith.dot" \
                  "$out/.semantic-source-files" \
                  "$PWD/FullCoupled/TheoremsMonolith.agda" \
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
                grep -Fq "requiredTheoremNames" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "requiredPlanComplete" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "inverse-correct" FullCoupled/TheoremsMonolith.agda
                grep -Fq "inverse-csearchable" FullCoupled/TheoremsMonolith.agda
                grep -Fq "inverse-preserves-csearchability" FullCoupled/TheoremsMonolith.agda
                grep -Fq "SearchableEquivalence" FullCoupled/TheoremsMonolith.agda
                ${canonicalGhc system}/bin/ghc \
                  -O0 \
                  -dcore-lint \
                  -i "$out" \
                  -odir "$out/ghc" \
                  -hidir "$out/ghc" \
                  -main-is FullCoupled.Agda2HsSemanticSearch.main \
                  -o "$out/agda2hs-semantic-search" \
                  "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                "$out/agda2hs-semantic-search" > "$out/report.txt"
                grep -Fq "True" "$out/report.txt"
                grep -E '^theorem-graph-edges=[1-9][0-9]* autonomous-a-star-chains=[1-9][0-9]*$' "$out/report.txt"
                grep -E '^agda2hs autonomous theorem-graph bounded DFS: [1-9][0-9]* dependency chains$' "$out/report.txt"
                grep -Fq "autonomous-regression=True" "$out/report.txt"
                grep -E "^semantic-laws=[1-9][0-9]* nonreflexive=[1-9][0-9]* composite=[1-9][0-9]*$" "$out/report.txt"
                grep -E "^required-plan-count=[1-9][0-9]* required-plan-total=[1-9][0-9]* required-plan-regression=True$" "$out/report.txt"
                grep -Fq "graphTwoLeafBranchesRegression" FullCoupled/Agda2HsSemanticSearch.agda
                grep -Fq "egraph-regression=True egraph-associativity-regression=True" "$out/report.txt"
                compiler_version=$("${canonicalGhc system}/bin/ghc" --numeric-version)
                printf '%s\n' \
                  "compiler=ghc-$compiler_version" \
                  "plugins=none" \
                  "proofKernel=Agda" \
                  "searchKernel=Agda2Hs" \
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
                pkgs.mirth
                pkgs.stdenv.cc
              ];
              text = ''
                set -euo pipefail
                out="build/agda-haskell"
                rm -rf "$out"
                mkdir -p "$out"
                "${agda2hsCommand system}/bin/agda2hs-ci" FullCoupled/Agda2HsSurface.agda -o "$out"
                test -s "$out/FullCoupled/Agda2HsSurface.hs"
                mkdir -p "$out/ghc"
                "${canonicalGhc system}/bin/ghc" ${builtins.concatStringsSep " " ghcLanguageFlags} -O0 -dcore-lint -package rio -i "$out" -odir "$out/ghc" -hidir "$out/ghc" -c "$out/FullCoupled/Agda2HsSurface.hs"
                liquid --version
                z3 --version
                printf '%s\n' \
                  "source=FullCoupled/Agda2HsSurface.agda generated=build/agda-haskell/FullCoupled/Agda2HsSurface.hs ghc:pass" \
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
              pkgs.mirth
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

          simple-haskell = pkgs.mkShell {
            packages = [
              (canonicalGhc system)
              pkgs.z3
            ];
            shellHook = ''
            '';
          };

          agda-ci = pkgs.mkShellNoCC {
            packages = [
              pkgs.dhall
              (agdaProofCommand system)
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
              export AGDA_COMMAND="agda-proof"
            '';
          };

          agda-versions = pkgs.mkShellNoCC {
            packages = [
              (canonicalGhc system)
              pkgs.dhall
              pkgs.z3
              pkgs.mirth
              (agdaProofCommand system)
              (agdaEmacs system)
            ];
            shellHook = ''
              export AGDA_COMMAND="agda-proof"
            '';
          };

          ci = pkgs.mkShell {
            packages = [
              pkgs.dhall
              (agdaProofCommand system)
              pkgs.z3
              pkgs.coreutils
              pkgs.findutils
              pkgs.git
              pkgs.gh
              pkgs.gnugrep
              pkgs.gnused
            ];
            shellHook = ''
              export AGDA_COMMAND="agda-proof"
            '';
          };

          default-versions = pkgs.mkShell {
            packages = [
              (canonicalGhc system)
              pkgs.dhall
              pkgs.z3
              pkgs.mirth
              pkgs.gh
              (agdaProofCommand system)
              (agdaEmacs system)
            ];
            shellHook = ''
              export AGDA_COMMAND="agda-proof"
            '';
          };

          default = pkgs.mkShell {
            packages = [
              pkgs.dhall
              (canonicalGhc system)
              pkgs.haskellPackages.cabal-install
              pkgs.z3
              pkgs.dhall-json
              pkgs.mirth
              pkgs.gh
              (agdaProofCommand system)
              (agdaEmacs system)
              pkgs.stdenv.cc
              pkgs.elmPackages.elm
            ];
            shellHook = ''
              export AGDA_COMMAND="agda-proof"
            '';
          };
        });
    };
}