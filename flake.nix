{
  description = "Q8.24 Agda learner, intuitionistic RUSS metatheory, and Teal Pages";

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

      # Share one GHC environment. Optimized GHC is for runtime builds;
      # ghc-check deliberately omits optimization flags for -fno-code checks.
      ghcEnvironment = system:
        let
          pkgs = pkgsFor system;
        in
        (pkgs.haskellPackages.ghcWithPackages.override {
          useLLVM = true;
        }) (ps: [ ps.ieee754 ps.vector ]);

      optimizedGhc = system:
        let
          pkgs = pkgsFor system;
          ghcEnv = ghcEnvironment system;
        in
        pkgs.writeShellScriptBin "ghc" ''
          exec "${ghcEnv}/bin/ghc" -O2 -fllvm "$@"
        '';

      checkGhc = system:
        let
          pkgs = pkgsFor system;
          ghcEnv = ghcEnvironment system;
        in
        pkgs.writeShellScriptBin "ghc-check" ''
          exec "${ghcEnv}/bin/ghc" "$@"
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

      tealLuaEnv = system:
        let
          pkgs = pkgsFor system;
          luafunPkg = luafunModule system;
        in
        pkgs.luajit.withPackages (_: [ luafunPkg ]);

      # Install pinned Teal and Lua Lanes into a project-local tree; LuaFun is pinned by Nix.
      luaRocksShellHook = pkgs: ''
        export AGDA_COMMAND="agda2hs-agda"
        export NIX_BUILD_CORES=1
        export MAKEFLAGS="-j1"
        export LUAROCKS_TREE="$PWD/.luarocks"
        export PATH="$LUAROCKS_TREE/bin:$PATH"
        export LUA_PATH="$LUAROCKS_TREE/share/lua/5.1/?.lua;$LUAROCKS_TREE/share/lua/5.1/?/init.lua;;"
        export LUA_CPATH="$LUAROCKS_TREE/lib/lua/5.1/?.so;;"
        mkdir -p "$LUAROCKS_TREE"
        if ! luarocks --tree "$LUAROCKS_TREE" show lanes >/dev/null 2>&1; then
          ${if pkgs.stdenv.isLinux then ''
            export PTHREAD_DIR="${pkgs.glibc.dev}"
            export PTHREAD_LIBDIR="${pkgs.glibc}/lib"
            luarocks --tree "$LUAROCKS_TREE" install lanes 3.17.2-0 PTHREAD_DIR="$PTHREAD_DIR" PTHREAD_LIBDIR="$PTHREAD_LIBDIR"
          '' else ''
            luarocks --tree "$LUAROCKS_TREE" install lanes 3.17.2-0
          ''}
        fi
        if ! luarocks --tree "$LUAROCKS_TREE" show tl >/dev/null 2>&1; then
          luarocks --tree "$LUAROCKS_TREE" install tl 0.24.8-1
        fi
      '';

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
            pkgs.gnugrep
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
            agda2hs_base_cache="''${XDG_CACHE_HOME:-$HOME/.cache}/agda2hs-base/$(basename "$agda2hs_base_root")"
            if [[ ! -f "$agda2hs_base_cache/.cache-source" ]] || [[ "$(cat "$agda2hs_base_cache/.cache-source" 2>/dev/null || true)" != "$agda2hs_base_root" ]]; then
              agda2hs_base_tmp="''${agda2hs_base_cache}.tmp"
              rm -rf "$agda2hs_base_tmp"
              mkdir -p "$(dirname "$agda2hs_base_cache")" "$agda2hs_base_tmp"
              cp -RL "$agda2hs_base_root/." "$agda2hs_base_tmp/"
              chmod -R u+rwX "$agda2hs_base_tmp"
              printf '%s\n' "$agda2hs_base_root" > "$agda2hs_base_tmp/.cache-source"
              rm -rf "$agda2hs_base_cache"
              mv "$agda2hs_base_tmp" "$agda2hs_base_cache"
            fi
            agda_version="$(agda2hs --disable-backend --numeric-version)"
            agda_data_root="''${XDG_CACHE_HOME:-$HOME/.cache}/agda-data/$agda_version"
            mkdir -p "$agda_data_root"
            export Agda_datadir="$agda_data_root"
            setup_agda_primitive_data() {
              agda2hs --disable-backend --setup
              local primitive_file="$Agda_datadir/lib/prim/Agda/Primitive.agda"
              if [[ ! -f "$primitive_file" ]]; then
                echo "Agda setup did not produce $primitive_file" >&2
                return 1
              fi
              if grep -Eq '(^|[[:space:]])--(rewriting|type-in-type)([[:space:]]|$)' "$primitive_file"; then
                echo "Agda primitive source contains project-only unsafe global options" >&2
                return 1
              fi
              echo "agda-primitive-setup=pass"
            }

            if [[ "$#" -eq 1 && "$1" == "--setup" ]]; then
              setup_agda_primitive_data
              exit $?
            fi
            if [[ ! -d "$Agda_datadir/lib/prim" ]]; then
              setup_agda_primitive_data
            fi
            if agda2hs --disable-backend "''${agda_global_options[@]}" -i "$agda2hs_base_cache" -i . "$@"; then
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
            pkgs.gnugrep
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
            agda2hs_base_cache="''${XDG_CACHE_HOME:-$HOME/.cache}/agda2hs-base/$(basename "$agda2hs_base_root")"
            if [[ ! -f "$agda2hs_base_cache/.cache-source" ]] || [[ "$(cat "$agda2hs_base_cache/.cache-source" 2>/dev/null || true)" != "$agda2hs_base_root" ]]; then
              agda2hs_base_tmp="''${agda2hs_base_cache}.tmp"
              rm -rf "$agda2hs_base_tmp"
              mkdir -p "$(dirname "$agda2hs_base_cache")" "$agda2hs_base_tmp"
              cp -RL "$agda2hs_base_root/." "$agda2hs_base_tmp/"
              chmod -R u+rwX "$agda2hs_base_tmp"
              printf '%s\n' "$agda2hs_base_root" > "$agda2hs_base_tmp/.cache-source"
              rm -rf "$agda2hs_base_cache"
              mv "$agda2hs_base_tmp" "$agda2hs_base_cache"
            fi
            agda_version="$(agda2hs --disable-backend --numeric-version)"
            agda_data_root="''${XDG_CACHE_HOME:-$HOME/.cache}/agda-data/$agda_version"
            mkdir -p "$agda_data_root"
            export Agda_datadir="$agda_data_root"
            setup_agda_primitive_data() {
              agda2hs --disable-backend --setup
              local primitive_file="$Agda_datadir/lib/prim/Agda/Primitive.agda"
              if [[ ! -f "$primitive_file" ]]; then
                echo "Agda setup did not produce $primitive_file" >&2
                return 1
              fi
              if grep -Eq '(^|[[:space:]])--(rewriting|type-in-type)([[:space:]]|$)' "$primitive_file"; then
                echo "Agda primitive source contains project-only unsafe global options" >&2
                return 1
              fi
              echo "agda-primitive-setup=pass"
            }

            if [[ "$#" -eq 1 && "$1" == "--setup" ]]; then
              setup_agda_primitive_data
              exit $?
            fi
            if [[ ! -d "$Agda_datadir/lib/prim" ]]; then
              setup_agda_primitive_data
            fi
            if agda2hs --disable-backend "''${agda_global_options[@]}" -i "$agda2hs_base_cache" -i . "$@"; then
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
            pkgs.gnugrep
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
            agda2hs_base_cache="''${XDG_CACHE_HOME:-$HOME/.cache}/agda2hs-base/$(basename "$agda2hs_base_root")"
            if [[ ! -f "$agda2hs_base_cache/.cache-source" ]] || [[ "$(cat "$agda2hs_base_cache/.cache-source" 2>/dev/null || true)" != "$agda2hs_base_root" ]]; then
              agda2hs_base_tmp="''${agda2hs_base_cache}.tmp"
              rm -rf "$agda2hs_base_tmp"
              mkdir -p "$(dirname "$agda2hs_base_cache")" "$agda2hs_base_tmp"
              cp -RL "$agda2hs_base_root/." "$agda2hs_base_tmp/"
              chmod -R u+rwX "$agda2hs_base_tmp"
              printf '%s\n' "$agda2hs_base_root" > "$agda2hs_base_tmp/.cache-source"
              rm -rf "$agda2hs_base_cache"
              mv "$agda2hs_base_tmp" "$agda2hs_base_cache"
            fi
            agda_version="$(agda2hs --disable-backend --numeric-version)"
            agda_data_root="''${XDG_CACHE_HOME:-$HOME/.cache}/agda-data/$agda_version"
            mkdir -p "$agda_data_root"
            export Agda_datadir="$agda_data_root"
            setup_agda_primitive_data() {
              agda2hs --disable-backend --setup
              local primitive_file="$Agda_datadir/lib/prim/Agda/Primitive.agda"
              if [[ ! -f "$primitive_file" ]]; then
                echo "Agda setup did not produce $primitive_file" >&2
                return 1
              fi
              if grep -Eq '(^|[[:space:]])--(rewriting|type-in-type)([[:space:]]|$)' "$primitive_file"; then
                echo "Agda primitive source contains project-only unsafe global options" >&2
                return 1
              fi
              echo "agda-primitive-setup=pass"
            }

            if [[ "$#" -eq 1 && "$1" == "--setup" ]]; then
              setup_agda_primitive_data
              exit $?
            fi
            if [[ ! -d "$Agda_datadir/lib/prim" ]]; then
              setup_agda_primitive_data
            fi
            if "${agda2hsTool system}/bin/agda2hs" "''${agda_global_options[@]}" --config "${./.ci/agda/agda2hs.yaml}" -i "$agda2hs_base_cache" -i . "$@"; then
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
        in {
          ci = { type = "app"; program = "${pkgs.dhall}/bin/dhall"; };
          agda = { type = "app"; program = "${agdaCli system}/bin/agda"; };
          agda2hs = { type = "app"; program = "${agda2hsCommand system}/bin/agda2hs"; };
          default = { type = "app"; program = "${agda2hsCommand system}/bin/agda2hs"; };
        });

      devShells = forAllSystems (system:
        let pkgs = pkgsFor system;
        in {
          agda-ci = pkgs.mkShell {
            packages = [
              (agdaCommand system)
              (agda2hsCommand system)
              pkgs.dhall
              pkgs.lessc
              pkgs.coreutils
              (tealLuaEnv system)
              pkgs.luajit
              pkgs.luajitPackages.luarocks-nix
              pkgs.stdenv.cc
              pkgs.gnumake
              (optimizedGhc system)
              (checkGhc system)
            ];
            shellHook = luaRocksShellHook pkgs;
          };

          presentation = pkgs.mkShell {
            packages = [
              pkgs.lessc
              pkgs.coreutils
              (tealLuaEnv system)
              pkgs.luajit
              pkgs.luajitPackages.luarocks-nix
            ];
            shellHook = luaRocksShellHook pkgs;
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

          default = pkgs.mkShell {
            packages = [
              (agdaCommand system)
              (agda2hsCommand system)
              pkgs.dhall
              pkgs.lessc
              pkgs.coreutils
              (tealLuaEnv system)
              pkgs.luajit
              pkgs.luajitPackages.luarocks-nix
              pkgs.stdenv.cc
              pkgs.gnumake
              (optimizedGhc system)
              (checkGhc system)
            ];
            shellHook = luaRocksShellHook pkgs;
          };
        });
    };
}
