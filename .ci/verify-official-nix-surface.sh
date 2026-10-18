#!/usr/bin/env bash
set -euo pipefail

for file in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$file" ] || continue
  ! grep -Eq 'DeterminateSystems|cachix|nix-community|install-nix-action|install-nix\.sh|curl[[:space:]].*(nixos\.org/nix/install|artifacts\.nixos\.org/nix-installer)|nix-env([[:space:]]|$)|nix[[:space:]]+profile[[:space:]]+install' "$file" || {
    echo "unsupported third-party Nix installer/cache reference: $file"
    exit 1
  }
done

! grep -Eq 'doJailbreak|allowBroken[[:space:]]*=|allowUnsupportedSystem[[:space:]]*=' flake.nix || {
  echo "unsupported Nix override present in flake.nix"
  exit 1
}

! grep -Eq 'nixpkgs-ghc924|inversion-plugin-src|cau-placc/inversion-plugin' flake.nix || {
  echo "legacy compiler/plugin input present in flake.nix"
  exit 1
}

grep -Fq 'github:NixOS/nixpkgs/' flake.nix
! grep -Eiq 'TypeTopology|typetopology' flake.nix || {
  echo "TypeTopology must not be in the active flake" >&2
  exit 1
}
input_count=$(grep -Ec '^[[:space:]]+(nixpkgs\.)?url[[:space:]]*=[[:space:]]*"github:' flake.nix)
[ "$input_count" -eq 5 ] || { echo "expected pinned main/Acorn Nixpkgs, official Acorn, its required Agda2HS fork, and Luafun inputs; found $input_count" >&2; exit 1; }
grep -Fq 'nixpkgs.url = "github:NixOS/nixpkgs/' flake.nix
grep -Fq 'acornNixpkgs.url = "github:NixOS/nixpkgs/205fd4226592cc83fd4c0885a3e4c9c400efabb5"' flake.nix
grep -Fq 'github:viktorcsimma/acorn/21b7624dbfb4ddd75418a0b037620ae4c8883cb2' flake.nix
grep -Fq 'github:viktorcsimma/agda2hs/a3c83ad3be876ce0c7aa31157f3107843bf2f465' flake.nix
grep -Fq 'acorn-reals = acornRealLibrary system;' flake.nix
grep -Fq 'name = "acorn-real-check";' flake.nix
grep -Fq 'github:luafun/luafun/02960048e4dff4f5fd5b683c4b61f9df42e8339f' flake.nix
! grep -Eiq 'acornprover|acornlib|xds-agda|xdsAgda|miniVehicle|vehicle-formalisation' flake.nix || {
  echo "unexpected auxiliary prover/semantics dependency in flake.nix" >&2
  exit 1
}

# One Dhall file owns policy text, workflow lanes and executable policy gates.
test -f .ci/actions_ci.dhall
! test -e .ci/pure-formal-stack.md
! test -e .ci/graph-search-contract.md
! test -e .ci/discovery/graph-search-spec.md

# Keep non-graph-search theorem material in the two designated monoliths.
for forbidden in \
  FullCoupled/ReflectionAutomation.agda \
  FullCoupled/FiniteTabularUAP.agda \
  FullCoupled/CircleHITInterface.agda; do
  test ! -e "$forbidden" || {
    echo "standalone non-graph-search proof module is forbidden: $forbidden" >&2
    exit 1
  }
done
grep -Fq 'github:luafun/luafun/02960048e4dff4f5fd5b683c4b61f9df42e8339f' flake.nix
grep -Fq 'name = "fennel-smoke";' flake.nix
grep -Fq 'name = "streamly-tools-check";' flake.nix
grep -Fq 'name = "agda-import-sync";' flake.nix
grep -Fq 'agda-emacs = agdaEmacs system;' flake.nix
grep -Fq 'agda = agdaCli system;' flake.nix
test -f .ci/lua/agda_import_sync.fnl
test -f .ci/agda/import-contracts.tsv
test -f .ci/agda/global-options.txt


! grep -Fq -- '-l agda2hs-base' flake.nix || { echo "do not require an unregistered Agda library name" >&2; exit 1; }
grep -Fq 'agda2hs_base_root' flake.nix || { echo "Agda2HS base source root must be explicit in wrappers" >&2; exit 1; }
[ "$(grep -Fc 'chmod -R u+rwX "$agda2hs_base_work/library"' flake.nix)" -eq 3 ] || {
  echo "Agda2HS base interface cache must be writable in all three wrappers" >&2
  exit 1
}


grep -Fq 'pkgs.luajitPackages.buildLuaPackage' flake.nix
grep -Fq 'pkgs.luajit.withPackages' flake.nix
grep -Fq 'name = "scott-strachey-domain-check";' flake.nix
grep -Fq 'name = "monoid-lstm-stream-check";' flake.nix
echo 'official-nix-surface=pass'
