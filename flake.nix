{
  description = "Pure Agda2HS extraction with separate Acorn, XDS-Agda, and MiniVehicle checks";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/0439f75413ace6c42e4c722cafd4d6e5401de648";
    acorn = {
      url = "github:acornprover/acorn/91f29ff1d25aff15afbde214dd9b620f817a9567";
      flake = false;
    };
    acornlib = {
      url = "github:acornprover/acornlib/7df4882d379d1cd0dc31136ea903b95ebe0d270e";
      flake = false;
    };
    xdsAgda = {
      url = "github:pdmosses/xds-agda/8e2acdbf4ae910b1a3e855d6bfd5271ff4a3fcff";
      flake = false;
    };
    miniVehicle = {
      url = "github:vehicle-lang/vehicle-formalisation/289f1940f9b11c293211ba2bc9fdf5c4c24e2b0a";
      flake = false;
    };
    luafun = {
      url = "github:luafun/luafun/02960048e4dff4f5fd5b683c4b61f9df42e8339f";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    acorn,
    acornlib,
    xdsAgda,
    miniVehicle,
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
          p.streamly-core
          p.streamly-shell
          p.streamly-coreutils
          p.streamly-process
        ]);

      acornProver = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.rustPlatform.buildRustPackage {
          pname = "acorn";
          version = "0.2.6";
          src = acorn;
          cargoLock.lockFile = "${acorn}/Cargo.lock";
          postUnpack = ''
            cp -a ${acornlib} "$sourceRoot/acornlib"
          '';
          nativeBuildInputs = [ pkgs.pkg-config ];
          buildInputs = [ pkgs.onnxruntime pkgs.openssl ];
          ORT_STRATEGY = "system";
          ORT_LIB_LOCATION = "${pkgs.onnxruntime}/lib";
          doCheck = false;
        };

      agdaCli = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.writeShellApplication {
          name = "agda";
          runtimeInputs = [
            (agdaWithPackages system)
            pkgs.coreutils
          ];
          text = ''
            mapfile -t agda_global_options < "${./.ci/agda/global-options.txt}"
            agda2hs_base_lib="$(find "${agda2hsBaseLib system}" -name '*.agda-lib' -print -quit)"
            if [[ -z "$agda2hs_base_lib" ]]; then
              echo "agda2hs-base .agda-lib not found in Nix package" >&2
              exit 1
            fi
            agda2hs_base_root="$(dirname "$agda2hs_base_lib")"
            exec "${agdaWithPackages system}/bin/agda" "''${agda_global_options[@]}" -i "$agda2hs_base_root" -i . "$@"
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
            mapfile -t agda_global_options < "${./.ci/agda/global-options.txt}"
            agda2hs_base_lib="$(find "${agda2hsBaseLib system}" -name '*.agda-lib' -print -quit)"
            if [[ -z "$agda2hs_base_lib" ]]; then
              echo "agda2hs-base .agda-lib not found in Nix package" >&2
              exit 1
            fi
            agda2hs_base_root="$(dirname "$agda2hs_base_lib")"
            exec agda "''${agda_global_options[@]}" -i "$agda2hs_base_root" -i . "$@"
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
          ];
          text = ''
            mapfile -t agda_global_options < "${./.ci/agda/global-options.txt}"
            agda2hs_base_lib="$(find "${agda2hsBaseLib system}" -name '*.agda-lib' -print -quit)"
            if [[ -z "$agda2hs_base_lib" ]]; then
              echo "agda2hs-base .agda-lib not found in Nix package" >&2
              exit 1
            fi
            agda2hs_base_root="$(dirname "$agda2hs_base_lib")"
            exec agda2hs "''${agda_global_options[@]}" -i "$agda2hs_base_root" -i . "$@"
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
          acorn-prover = acornProver system;
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
          fennel-smoke = let
            script = pkgs.writeShellApplication {
              name = "fennel-smoke";
              runtimeInputs = [ (fennelRuntime system) pkgs.luajit pkgs.coreutils pkgs.gnugrep ];
              text = ''
                set -euo pipefail
                LUA_PATH="${luafunModule system}/share/lua/5.1/?.lua;;" \
                  luajit -e 'local fun = require("fun"); assert(type(fun.map) == "function")'
                fennel --version
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                printf '%s\n' '(print "fennel-luajit=pass")' > "$tmp/smoke.fnl"
                test "$(fennel "$tmp/smoke.fnl")" = "fennel-luajit=pass"
                echo "fennel-luajit-smoke=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/fennel-smoke";
          };

          agda-import-sync = let
            script = pkgs.writeShellApplication {
              name = "agda-import-sync";
              runtimeInputs = [ (fennelRuntime system) pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                exec ${fennelRuntime system}/bin/fennel .ci/lua/agda_import_sync.fnl "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/agda-import-sync";
          };

          fennel-agda-graph = let
            script = pkgs.writeShellApplication {
              name = "fennel-agda-graph";
              runtimeInputs = [ (fennelRuntime system) pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                exec ${fennelRuntime system}/bin/fennel .ci/lua/agda_graph.fnl "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/fennel-agda-graph";
          };

          fennel-ascii-surface = let
            script = pkgs.writeShellApplication {
              name = "fennel-ascii-surface";
              runtimeInputs = [ (fennelRuntime system) pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                exec ${fennelRuntime system}/bin/fennel .ci/lua/ascii_surface.fnl "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/fennel-ascii-surface";
          };

          fennel-surface = let
            script = pkgs.writeShellApplication {
              name = "fennel-surface";
              runtimeInputs = [ (fennelRuntime system) pkgs.coreutils ];
              text = ''
                set -euo pipefail
                exec ${fennelRuntime system}/bin/fennel .ci/lua/agda_surface.fnl "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/fennel-surface";
          };

          streamly-tools-check = let
            script = pkgs.writeShellApplication {
              name = "streamly-tools-check";
              runtimeInputs = [ (streamlyGhc system) pkgs.coreutils pkgs.gnugrep ];
              text = ''
                set -euo pipefail
                ghc --numeric-version
                packages="$(ghc-pkg list)"
                for package in streamly streamly-core streamly-shell streamly-coreutils streamly-process; do
                  grep -Fq -- "$package-" <<< "$packages" || {
                    echo "missing Nix-provided Haskell package: $package" >&2
                    exit 1
                  }
                done
                echo "streamly-nix-packages=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/streamly-tools-check";
          };

          acorn-smoke = let
            script = pkgs.writeShellApplication {
              name = "acorn-smoke";
              runtimeInputs = [ (acornProver system) ];
              text = ''
                set -euo pipefail
                acorn --version
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/acorn-smoke";
          };

          xds-agda-check = let
            script = pkgs.writeShellApplication {
              name = "xds-agda-check";
              runtimeInputs = [ (agdaWithStandardLibrary system) pkgs.coreutils ];
              text = ''
                set -euo pipefail
                agda --version
                agda -i "${xdsAgda}/agda" "${xdsAgda}/agda/LC/Tests.lagda"
                agda -i "${xdsAgda}/agda" "${xdsAgda}/agda/PCF/Checks.lagda"
                agda -i "${xdsAgda}/agda" "${xdsAgda}/agda/Scm/Soundness-Tests.lagda"
                echo "xds-agda-check=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/xds-agda-check";
          };

          mini-vehicle-check = let
            script = pkgs.writeShellApplication {
              name = "mini-vehicle-check";
              runtimeInputs = [ (agdaWithStandardLibrary system) pkgs.coreutils ];
              text = ''
                set -euo pipefail
                agda -i "${miniVehicle}/src" "${miniVehicle}/src/Everything.agda"
                echo "mini-vehicle-check=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/mini-vehicle-check";
          };

          scott-strachey-domain-check = let
            script = pkgs.writeShellApplication {
              name = "scott-strachey-domain-check";
              runtimeInputs = [ (agdaCommand system) ];
              text = ''
                set -euo pipefail
                agda2hs-agda -i . FullCoupled/FormalMethods/ScottStracheyDomains.agda
                echo "scott-strachey-domain-check=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/scott-strachey-domain-check";
          };

          monoid-lstm-stream-check = let
            script = pkgs.writeShellApplication {
              name = "monoid-lstm-stream-check";
              runtimeInputs = [ (agdaCommand system) ];
              text = ''
                set -euo pipefail
                agda2hs-agda -i . FullCoupled/FormalMethods/MonoidLSTMStreams.agda
                echo "monoid-lstm-stream-check=pass"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/monoid-lstm-stream-check";
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
                # Historical theorem monoliths are outside this kernel-checked target.
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
                grep -Fxq "graph-cycle-rejected=True" "$out/report.txt"
                grep -Fxq "graph-linear-chain=True" "$out/report.txt"
                grep -Fxq "graph-search-contract=True" "$out/report.txt"

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
                                    -i "$out" \
                  -odir "$out/ghc" \
                  -hidir "$out/ghc" \
                  -main-is FullCoupled.Agda2HsSemanticSearch.main \
                  -o "$out/agda2hs-semantic-search" \
                  "$out/FullCoupled/Agda2HsSemanticSearch.hs"
                "$out/agda2hs-semantic-search" > "$out/report.txt"
                grep -Fq "True" "$out/report.txt"
                grep -E '^theorem-graph-edges=[1-9][0-9]* autonomous-depth-first-chains=[1-9][0-9]*$' "$out/report.txt"
                grep -E '^agda2hs autonomous theorem-graph DFS: [1-9][0-9]* maximal dependency chains$' "$out/report.txt"
                grep -Fq "autonomous-regression=True" "$out/report.txt"
                grep -Fq "graph-branch-regression=True" "$out/report.txt"
                grep -Fq "graph-two-leaf-paths=True" "$out/report.txt"
                grep -Fq "graph-cycle-rejected=True" "$out/report.txt"
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
                "${canonicalGhc system}/bin/ghc" ${builtins.concatStringsSep " " ghcLanguageFlags} -O0 -dcore-lint -i "$out" -odir "$out/ghc" -hidir "$out/ghc" -c "$out/FullCoupled/Agda2HsSurface.hs"
                mkdir -p "$out/ghc-search"
                "${canonicalGhc system}/bin/ghc" \
                  -O0 -dcore-lint -i "$out" \
                  -odir "$out/ghc-search" -hidir "$out/ghc-search" \
                  -main-is FullCoupled.Agda2HsGraphSearchCheck.main \
                  -o "$out/graph-search-check" \
                  "$out/FullCoupled/Agda2HsGraphSearchCheck.hs"
                "$out/graph-search-check" > "$out/graph-search-report.txt"
                grep -Fxq "graph-two-leaf-branches=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-dependency-order=True" "$out/graph-search-report.txt"
                grep -Fxq "graph-best-first-tie=True" "$out/graph-search-report.txt"
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