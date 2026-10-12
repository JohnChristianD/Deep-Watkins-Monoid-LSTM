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
[ "$input_count" -eq 5 ] || { echo "expected five pinned inputs, found $input_count" >&2; exit 1; }
grep -Fq 'nixpkgs.url = "github:NixOS/nixpkgs/' flake.nix
grep -Fq 'github:acornprover/acorn/' flake.nix
grep -Fq 'github:acornprover/acornlib/' flake.nix
grep -Fq 'github:pdmosses/xds-agda/' flake.nix
grep -Fq 'github:vehicle-lang/vehicle-formalisation/' flake.nix
grep -Fq 'acorn-prover = acornProver system;' flake.nix
grep -Fq 'name = "xds-agda-check";' flake.nix
grep -Fq 'name = "mini-vehicle-check";' flake.nix
echo 'official-nix-surface=pass'
