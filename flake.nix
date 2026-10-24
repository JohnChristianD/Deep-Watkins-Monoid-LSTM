{
  description = "Canonical Agda learner, intuitionistic RUSS metatheory, and static Fennel Pages";

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
          integer_source="$(find "$out" -path '*/Haskell/Law/Num/Integer.agda' -print -quit)"
          test -n "$integer_source" || {
            echo "Haskell/Law/Num/Integer.agda not found in pinned agda2hs-base" >&2
            exit 1
          }
          # Upstream subNat-distrib-minus-cong-+ drops one successor in its
          # common-offset proof. Agda 2.8 exposes the resulting mismatch.
          python - "$integer_source" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_text()
old = "subNat-cong-+ m (n * suc m) (o * suc m)"
new = "subNat-cong-+ (suc m) (n * suc m) (o * suc m)"
if source.count(old) != 1:
    raise SystemExit("pinned Haskell.Law.Num.Integer common-offset proof changed; refusing a fuzzy edit")
path.write_text(source.replace(old, new, 1))
PY
          grep -Fq 'subNat-cong-+ (suc m) (n * suc m) (o * suc m)' "$integer_source"
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
            # Keep information-only invocations independent of source compilation.
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
            # Keep information-only invocations independent of source compilation.
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
        let pkgs = pkgsFor system;
        in {
          agda = agdaCli system;
          agda2hs = agda2hsTool system;
          agda-emacs = agdaEmacs system;
          ci = pkgs.dhall;
          default = agdaCli system;
        });

      apps = forAllSystems (system:
        let
          pkgs = pkgsFor system;
          laneApp = lane:
            let
              script = pkgs.writeShellApplication {
                name = "run-agda-lane";
                runtimeInputs = [
                  (agdaCommand system)
                  (fennelRuntime system)
                  pkgs.lessc
                  pkgs.coreutils
                  pkgs.dhall
                ];
                text = ''
                  set -euo pipefail
                  exec fennel .ci/fennel/ci.fnl ${lane}
                '';
              };
            in {
              type = "app";
              program = "${script}/bin/run-agda-lane";
            };
        in {
          ci = { type = "app"; program = "${pkgs.dhall}/bin/dhall"; };
          agda-learner-check = laneApp "AgdaLearner";
          agda-theorem-check = laneApp "AgdaTheorem";
          russ-audit = laneApp "RUSS";
          pages = laneApp "Pages";
          default = { type = "app"; program = "${agdaCli system}/bin/agda"; };
        });

      devShells = forAllSystems (system:
        let pkgs = pkgsFor system;
        in {
          agda-ci = pkgs.mkShellNoCC {
            packages = [
              (agdaCommand system)
              (fennelRuntime system)
              pkgs.dhall
              pkgs.lessc
              pkgs.coreutils
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };

          presentation = pkgs.mkShellNoCC {
            packages = [
              (fennelRuntime system)
              pkgs.lessc
              pkgs.coreutils
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

          default = pkgs.mkShellNoCC {
            packages = [
              (agdaCommand system)
              (fennelRuntime system)
              pkgs.dhall
              pkgs.lessc
              pkgs.coreutils
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };
        });
    };
}
