{
  description = "Agda2HS RUSS semantics and immutable Fennel/Pages build";

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

      # ccforth is not in the pinned Nixpkgs revision. Package the upstream
      # v0.3.2 release archive with a fixed SHA-256 per supported system.
      # This keeps the tool in the Nix store and avoids runtime go-install.
      # Gforth's bundled SWIG-Forth fork needs pcre-config during configure.
      # Nixpkgs places PCRE in buildInputs, which does not guarantee the helper
      # is on PATH for this native build tool. Add it explicitly as a native
      # build input without changing upstream source or the pinned package set.
      gforth = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.gforth.overrideAttrs (old: {
          nativeBuildInputs = map
            (input:
              if (input.pname or "") == "swig"
                && builtins.match ".*forth.*" (input.version or "") != null
              then
                input.overrideAttrs (swigOld: {
                  nativeBuildInputs =
                    (swigOld.nativeBuildInputs or [ ]) ++ [ pkgs.pcre ];
                })
              else
                input)
            old.nativeBuildInputs;
        });

      ccforth = system:
        let
          pkgs = pkgsFor system;
          release = {
            "x86_64-linux" = {
              file = "ccforth_0.3.2_linux_amd64.tar.gz";
              hash = "5cd2a960474d7ff693853040551fd48c0e8623024ec877302822cd1e275695a7";
            };
            "aarch64-linux" = {
              file = "ccforth_0.3.2_linux_arm64.tar.gz";
              hash = "f5c566f7b6dcd295431bf8eb50f5702532d1177e42bcaf6b175109449db7e722";
            };
            "x86_64-darwin" = {
              file = "ccforth_0.3.2_darwin_amd64.tar.gz";
              hash = "36f90a77fe85f3291945201c2ddad75a00afeb5e5ecaacdfb683cd5d79657b4f";
            };
            "aarch64-darwin" = {
              file = "ccforth_0.3.2_darwin_arm64.tar.gz";
              hash = "8bece38e0d547754fa2a73fcb7d94510910dc2511f72183fea8dcebe0f222af0";
            };
          }.${system} or (throw "ccforth v0.3.2 has no release archive for ${system}");
          archive = pkgs.fetchurl {
            url = "https://github.com/ncw/ccforth/releases/download/v0.3.2/${release.file}";
            sha256 = release.hash;
          };
        in
        pkgs.stdenvNoCC.mkDerivation {
          pname = "ccforth";
          version = "0.3.2";
          src = archive;
          sourceRoot = ".";
          dontConfigure = true;
          dontBuild = true;
          installPhase = ''
            runHook preInstall
            mkdir -p "$out/bin"
            binary="$(find . -type f -name ccforth -print -quit)"
            test -n "$binary" || {
              echo "ccforth executable missing from pinned upstream archive" >&2
              exit 1
            }
            install -m 755 "$binary" "$out/bin/ccforth"
            runHook postInstall
          '';
          doInstallCheck = true;
          installCheckPhase = ''
            "$out/bin/ccforth" -version
          '';
          meta = {
            description = "Forth 2012 to C compiler";
            homepage = "https://github.com/ncw/ccforth";
            license = pkgs.lib.licenses.mit;
            mainProgram = "ccforth";
            platforms = [
              "x86_64-linux"
              "aarch64-linux"
              "x86_64-darwin"
              "aarch64-darwin"
            ];
          };
        };

      # The Forth fork predates Agda 2.8. Apply a small API-port patch before
      # Cabal resolves the package, so its dependency bounds and source agree.
      agda2forthSource = builtins.fetchGit {
        url = "https://github.com/LMMilliken/agda2Forth.git";
        rev = "e83f8cc735bf220f80b3655ce2158a23818910fe";
      };

      agda2forth = system:
        let
          pkgs = pkgsFor system;
          source = pkgs.applyPatches {
            name = "agda2forth-agda-2.8";
            src = agda2forthSource;
            patches = [ ./nix/patches/agda2forth-agda-2.8.patch ];
          };
        in
        pkgs.haskellPackages.callCabal2nix "agda2forth" source { };

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

      agdaWithPackages = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agda.withPackages {
          pkgs = [
            (agda2hsBaseLib system)
          ];
        };

      agdaWithStandardLibrary = system:
        let
          pkgs = pkgsFor system;
        in
        pkgs.agda.withPackages {
          pkgs = [ pkgs.agdaPackages.standard-library ];
        };

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

      fennelJitEnv = system:
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
          luaEnv = fennelJitEnv system;
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
            # Information-only calls must not inherit the project backend (--js).
            # The JS backend expects an input module, unlike --version and --help.
            if [[ "$#" -eq 1 && ( "$1" == "--version" || "$1" == "-V" || "$1" == "--help" || "$1" == "-h" ) ]]; then
              exec agda "$@"
            fi
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
            # Information-only calls must not inherit the project backend (--js).
            # The JS backend expects an input module, unlike --version and --help.
            if [[ "$#" -eq 1 && ( "$1" == "--version" || "$1" == "-V" || "$1" == "--help" || "$1" == "-h" ) ]]; then
              exec agda "$@"
            fi
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
            (agda2hsTool system)
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
          agda2forth = agda2forth system;
          agda2hs = agda2hsTool system;
          agda-emacs = agdaEmacs system;
          ccforth = ccforth system;
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
          fennel-monolith-content = let
            script = pkgs.writeShellApplication {
              name = "fennel-monolith-content";
              runtimeInputs = [ (fennelRuntime system) pkgs.coreutils pkgs.git ];
              text = ''
                set -euo pipefail
                exec ${fennelRuntime system}/bin/fennel .ci/fennel/monolith_catalog.fnl "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/fennel-monolith-content";
          };

          fennel-palette-css = let
            script = pkgs.writeShellApplication {
              name = "fennel-palette-css";
              runtimeInputs = [ (fennelRuntime system) pkgs.coreutils ];
              text = ''
                set -euo pipefail
                exec ${fennelRuntime system}/bin/fennel .ci/fennel/palette_css.fnl "$@"
              '';
            };
          in {
            type = "app";
            program = "${script}/bin/fennel-palette-css";
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
              (agdaCommand system)
              pkgs.scsh
              pkgs.luajit
              pkgs.coreutils
              pkgs.findutils
              pkgs.gawk
              pkgs.git
              pkgs.gnugrep
              pkgs.gnused
              pkgs.lessc
              pkgs.nodejs
              pkgs.dhall
              pkgs.dhall-json
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
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
              (pkgs.haskellPackages.ghc)
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

          # The Forth path is Agda2Forth -> .fth -> ccforth/GCC.
          # Keep GForth as the reference runtime and scsh as the smoke runner.
          forth = pkgs.mkShell {
            packages = [
              (agda2forth system)
              (ccforth system)
              (gforth system)
              pkgs.groff
              pkgs.scsh
              pkgs.gcc
              pkgs.coreutils
              pkgs.findutils
              pkgs.gnugrep
              pkgs.gnused
            ];
          };

          agda-ci = pkgs.mkShellNoCC {
            packages = [
              pkgs.scsh
              pkgs.git
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
              (pkgs.haskellPackages.ghc)
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
              (pkgs.haskellPackages.ghc)
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
              (pkgs.haskellPackages.ghc)
              pkgs.haskellPackages.cabal-install
              pkgs.z3
              pkgs.dhall-json
              pkgs.gh
              (agdaCommand system)
              (agdaEmacs system)
              pkgs.stdenv.cc
              (ccforth system)
              (gforth system)
              pkgs.groff
              pkgs.scsh
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };
        });
    };
}