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
                printf '%s\n' \
                  '(local fun (require :fun))' \
                  '(local mapped (fun.totable (fun.map (fn [n] (* n 2)) (ipairs [1 2 3]))))' \
                  '(assert (= (table.concat mapped ",") "2,4,6"))' \
                  '(print "fennel-luafun=pass")' > "$tmp/smoke.fnl"
                test "$(fennel "$tmp/smoke.fnl")" = "fennel-luafun=pass"
                echo "fennel-luajit-luafun-smoke=pass"
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
                # streamly-process-0.3.1 is marked broken in this pinned nixpkgs.
                # Keep the smoke check limited to evaluable Streamly core packages.
                for package in streamly streamly-bytestring streamly-core; do
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
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                awk '
                  /^module ScottStracheyDomains where$/ { capture=1; print; next }
                  /^-- Re-export policy semantics proved beside the canonical learner transition/ { capture=0 }
                  capture { sub(/^  /, ""); print }
                ' FullCoupled/TheoremsMonolith.agda > "$tmp/ScottStracheyDomains.agda"
                awk '
                  /^module BetaOptimalityBoundary where$/ { capture=1; print; next }
                  /^module CanonicalBellmanOrderTheory where$/ { capture=0 }
                  capture { sub(/^  /, ""); print }
                ' FullCoupled/CanonicalLearnerMonolith.agda > "$tmp/BetaOptimalityBoundary.agda"
                awk '
                  /^module LawvereDiagonal where$/ { capture=1; print; next }
                  /^-- Re-export policy semantics proved beside the canonical learner transition/ { capture=0 }
                  capture { sub(/^  /, ""); print }
                ' FullCoupled/TheoremsMonolith.agda > "$tmp/LawvereDiagonal.agda"
                awk '
                  /^module CanonicalBellmanOrderTheory where$/ { capture=1; print; next }
                  capture { sub(/^  /, ""); print }
                ' FullCoupled/CanonicalLearnerMonolith.agda > "$tmp/CanonicalBellmanOrderTheory.agda"
                test -s "$tmp/ScottStracheyDomains.agda"
                test -s "$tmp/BetaOptimalityBoundary.agda"
                test -s "$tmp/CanonicalBellmanOrderTheory.agda"
                test -s "$tmp/LawvereDiagonal.agda"
                for extracted in \
                  "$tmp/ScottStracheyDomains.agda" \
                  "$tmp/BetaOptimalityBoundary.agda" \
                  "$tmp/LawvereDiagonal.agda"; do
                  grep -Fq "open import Haskell.Prelude" "$extracted"
                  if grep -Fq "Agda.Builtin." "$extracted"; then
                    echo "forbidden Agda.Builtin import in $extracted" >&2
                    exit 1
                  fi
                done
                grep -Fq "lawvereFixedPoint" "$tmp/LawvereDiagonal.agda"
                grep -Fq "noSurjectiveBooleanDiagonal" "$tmp/LawvereDiagonal.agda"
                grep -Fq "denotationalCompositionalityRegression" "$tmp/ScottStracheyDomains.agda"
                grep -Fq "denotationalBottomStrictnessRegression" "$tmp/ScottStracheyDomains.agda"
                grep -Fq "scottErshovNLabDenotationalSemanticsRegression" "$tmp/ScottStracheyDomains.agda"
                grep -Fq "liftStrictMapBottom" "$tmp/ScottStracheyDomains.agda"
                grep -Fq "NeuralPolicyMDP" "$tmp/CanonicalBellmanOrderTheory.agda"
                grep -Fq "neuralBellmanOptimalValueIsLeast" "$tmp/CanonicalBellmanOrderTheory.agda"
                grep -Fq "neuralPolicyGreedyOptimalAtBellmanValue" "$tmp/CanonicalBellmanOrderTheory.agda"
                grep -Fq "neuralBellmanValueIsSupremumOfQStar" "$tmp/CanonicalBellmanOrderTheory.agda"
                agda2hs-agda -i "$tmp" "$tmp/ScottStracheyDomains.agda"
                agda2hs-agda -i "$tmp" "$tmp/BetaOptimalityBoundary.agda"
                agda2hs-agda -i "$tmp" "$tmp/CanonicalBellmanOrderTheory.agda"
                agda2hs-agda -i "$tmp" "$tmp/LawvereDiagonal.agda"
                echo "scott-strachey-domain-check=pass (Scott domains, compositionality/strictness regression, and Lawvere boundary kernel-checked)"
                echo "beta-optimality=kernel-checked (exact-maximal implies beta-optimal; universal fixed-choice impossibility)"
                echo "bellman-order-theory=kernel-checked (Tarski, omega-Kleene, neural MDP Bellman, exact-Q greedy optimality)"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/scott-strachey-domain-check";
          };

          monoid-lstm-stream-check = let
            script = pkgs.writeShellApplication {
              name = "monoid-lstm-stream-check";
              runtimeInputs = [ (agdaCommand system) (agda2hsCommand system) (canonicalGhc system) pkgs.coreutils pkgs.gnugrep ];
              text = ''
                set -euo pipefail
                repo_root=$PWD
                out="$repo_root/build/monoid-lstm-stream-check"
                rm -rf "$out"
                mkdir -p "$out"
                tmp=$(mktemp -d)
                trap 'rm -rf "$tmp"' EXIT
                mkdir -p "$tmp/FullCoupled"

                # This test wrapper avoids compiling the legacy owner monolith
                # (whose protected --level-universe import closure is incompatible
                # with Haskell.Prelude). The actual source still owns the nested
                # module; the wrapper has a unique top-level name to avoid collisions.
                # Never create MonoidLSTMStreams.agda or MonoidLSTMStreams.hs.
                source=FullCoupled/CanonicalLearnerMonolith.agda
                target="$tmp/FullCoupled/StreamCheck.agda"
                printf '%s\n' \
                  '{-# OPTIONS --sized-types --no-guardedness #-}' \
                  'module FullCoupled.StreamCheck where' > "$target"
                awk '
                  /^module MonoidLSTMStreams where$/ { capture=1; print; next }
                  /^module MLS = MonoidLSTMStreams$/ { capture=0; exit }
                  capture && /^------------------------------------------------------------------------/ { capture=0; exit }
                  capture { sub(/^  /, ""); print }
                ' "$source" >> "$target"

                grep -Fq 'module FullCoupled.StreamCheck where' "$target"
                grep -Fq 'module MonoidLSTMStreams where' "$target"
                grep -Fq 'runningSumPrefixRegression = refl' "$target"
                grep -Fq 'canonicalLearnerTracePrefix' "$source"
                grep -Fq 'canonicalTotalCountAfter' "$source"
                grep -Fq 'open import Haskell.Prim.Thunk' "$target"
                if grep -Fq 'open import Agda.Builtin.Coinduction' "$target" ||
                   grep -Fq 'import Agda.Builtin.Coinduction' "$target"; then
                  echo "stream calculus must use Agda2HS Thunk coinduction" >&2
                  exit 1
                fi

                # Run from the temporary root: the wrapper resolves module
                # names through include roots, not the absolute target filename.
                cd "$tmp"
                agda2hs-agda -i . -i "$repo_root" FullCoupled/StreamCheck.agda
                agda2hs-ci FullCoupled/StreamCheck.agda -o "$out"
                test -s "$out/FullCoupled/StreamCheck.hs"
                mkdir -p "$out/ghc"
                ghc -fno-code -i"$out" -odir "$out/ghc" -hidir "$out/ghc" \
                  "$out/FullCoupled/StreamCheck.hs"
                if find "$tmp" "$out" -name 'MonoidLSTMStreams.agda' -o -name 'MonoidLSTMStreams.hs' | grep -q .; then
                  echo "stream module must not become its own generated source/object" >&2
                  exit 1
                fi
                echo "monoid-lstm-stream-check=pass (nested stream, owner-module Agda2HS/GHC smoke test)"
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