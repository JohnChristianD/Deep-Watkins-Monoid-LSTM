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
[ "$input_count" -eq 6 ] || { echo "expected six pinned inputs, found $input_count" >&2; exit 1; }
grep -Fq 'nixpkgs.url = "github:NixOS/nixpkgs/' flake.nix
grep -Fq 'github:acornprover/acorn/' flake.nix
grep -Fq 'github:acornprover/acornlib/' flake.nix
grep -Fq 'github:pdmosses/xds-agda/' flake.nix
grep -Fq 'github:vehicle-lang/vehicle-formalisation/' flake.nix
grep -Fq 'github:luafun/luafun/02960048e4dff4f5fd5b683c4b61f9df42e8339f' flake.nix
grep -Fq 'name = "fennel-smoke";' flake.nix
grep -Fq 'name = "streamly-tools-check";' flake.nix
grep -Fq 'name = "agda-import-sync";' flake.nix
grep -Fq 'agda-emacs = agdaEmacs system;' flake.nix
grep -Fq 'agda = agdaCli system;' flake.nix
test -f .ci/lua/agda_import_sync.fnl
test -f .ci/agda/import-contracts.tsv
test -f .ci/agda/global-options.txt
grep -Fxq -- '--erasure' .ci/agda/global-options.txt
grep -Fxq -- '--no-projection-like' .ci/agda/global-options.txt

# The legacy monoliths are source-inventory-only until their stale imports are
# ported. Even so, do not let an inconsistent/untrusted option set accumulate.
for source in FullCoupled/CanonicalLearnerMonolith.agda FullCoupled/LearnerLogicalSpec.agda; do
  if grep -Eq '^[[:space:]]*--(no-fast-reduce|no-termination-check|type-in-type|no-positivity-check|large-indices|forced-argument-recursion|omega-in-omega|no-omega-in-omega)([[:space:]]|$)' "$source"; then
    echo "unsafe or incompatible Agda option remains in $source" >&2
    exit 1
  fi
done
! grep -E 'exec (agda|agda2hs) .*--(erasure|no-projection-like)' flake.nix || { echo "global Agda flags must come from .ci/agda/global-options.txt" >&2; exit 1; }
! grep -Eiq 'p[.]rio|-package rio|mirth|TypeTopology|typetopology' flake.nix || { echo "retired compiler dependency remains in active flake" >&2; exit 1; }
grep -Fq 'pkgs.luajitPackages.buildLuaPackage' flake.nix
grep -Fq 'pkgs.luajit.withPackages' flake.nix
grep -Fq 'acorn-prover = acornProver system;' flake.nix
grep -Fq 'name = "xds-agda-check";' flake.nix
grep -Fq 'name = "mini-vehicle-check";' flake.nix
grep -Fq 'name = "scott-strachey-domain-check";' flake.nix
grep -Fq 'name = "monoid-lstm-stream-check";' flake.nix
echo 'official-nix-surface=pass'
