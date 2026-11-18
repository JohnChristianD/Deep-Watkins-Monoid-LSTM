{
  description = "Canonical Agda learner, intuitionistic RUSS metatheory, and static Fennel Pages";

  inputs = {
    # Match the Nixpkgs revision used by the upstream Agda 2.9 agda2hs build.
    nixpkgs.url = "github:NixOS/nixpkgs/2074cc672349f14240fb7ea90d509e0b643e9dd4";

    # Upstream agda2hs Agda-2.9 port (PR #474), pinned to its reviewed head.
    agda2hs-upstream = {
      url = "github:jespercockx/agda2hs/2f89c9adc5018aa34bf4ed715750d30c088fdcb7";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    luafun = {
      url = "github:luafun/luafun/02960048e4dff4f5fd5b683c4b61f9df42e8339f";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    luafun,
    agda2hs-upstream
  }:    let
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

      # Use upstream agda2hs and its own Agda-2.9 base library.
      agda2hsBaseLib = system:
        agda2hs-upstream.packages.${system}.base-lib;

      # Build the upstream Haskell package set's GHC wrapper with LLVM enabled.
      # Keep the requested backend/optimization flags to exactly -O2 -fllvm.
      optimizedGhc = system:
        let
          pkgs = pkgsFor system;
          ghcEnv = (pkgs.haskellPackages.ghcWithPackages.override {
            useLLVM = true;
          }) (ps: [ ps.ieee754 ]);
        in
        pkgs.writeShellScriptBin "ghc" ''
          exec "${ghcEnv}/bin/ghc" -O2 -fllvm "$@"
        '';

      agda2hsTool = system:
        let
          upstream = agda2hs-upstream.packages.${system}.agda2hs;
        in
        upstream.withPackages {
          pkgs = [ (agda2hsBaseLib system) ];
          ghc = optimizedGhc system;
        };

      agdaEmacs = system:
        let
          pkgs = pkgsFor system;
        in
        (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (epkgs: [
          epkgs.agda2-mode
        ]);

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
            (agda2hsTool system)
            pkgs.coreutils
            pkgs.findutils
            (optimizedGhc system)
          ];
          text = ''
            # Keep information-only invocations independent of source compilation.
            if [[ "$#" -eq 1 && ( "$1" == "--version" || "$1" == "-V" || "$1" == "--help" || "$1" == "-h" ) ]]; then
              exec agda2hs --disable-backend "$@"
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
            if agda2hs --disable-backend "''${agda_global_options[@]}" -i "$agda2hs_base_work/library" -i . "$@"; then
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
            (agda2hsTool system)
            pkgs.coreutils
            pkgs.findutils
            (optimizedGhc system)
          ];
          text = ''
            # Keep information-only invocations independent of source compilation.
            if [[ "$#" -eq 1 && ( "$1" == "--version" || "$1" == "-V" || "$1" == "--help" || "$1" == "-h" ) ]]; then
              exec agda2hs --disable-backend "$@"
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
            if agda2hs --disable-backend "''${agda_global_options[@]}" -i "$agda2hs_base_work/library" -i . "$@"; then
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
          name = "agda2hs";
          runtimeInputs = [
            (agda2hsTool system)
            pkgs.coreutils
            pkgs.findutils
            (optimizedGhc system)
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
            if "${agda2hsTool system}/bin/agda2hs" "''${agda_global_options[@]}" --config "${./.ci/agda/agda2hs.yaml}" -i "$agda2hs_base_work/library" -i . "$@"; then
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
          agda2hs = agda2hsCommand system;
          agda-emacs = agdaEmacs system;
          ci = pkgs.dhall;
          default = agda2hsCommand system;
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
          agda = { type = "app"; program = "${agdaCli system}/bin/agda"; };
          agda2hs = { type = "app"; program = "${agda2hsCommand system}/bin/agda2hs"; };
          agda-learner-check = laneApp "AgdaLearner";
          agda-theorem-check = laneApp "AgdaTheorem";
          russ-audit = laneApp "RUSS";
          pages = laneApp "Pages";
          default = { type = "app"; program = "${agda2hsCommand system}/bin/agda2hs"; };
        });

      devShells = forAllSystems (system:
        let pkgs = pkgsFor system;
        in {
          agda-ci = pkgs.mkShellNoCC {
            packages = [
              (agdaCommand system)
              (agda2hsCommand system)
              (fennelRuntime system)
              pkgs.dhall
              pkgs.lessc
              pkgs.coreutils
              (optimizedGhc system)
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

          agda-emacs = pkgs.mkShellNoCC {
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
              (agda2hsCommand system)
              (fennelRuntime system)
              pkgs.dhall
              pkgs.lessc
              pkgs.coreutils
              (optimizedGhc system)
            ];
            shellHook = ''
              export AGDA_COMMAND="agda2hs-agda"
            '';
          };
        });
    };
}
