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
input_count=$(grep -Ec '^[[:space:]]+([[:alnum:]_-]+[.])?url[[:space:]]*=[[:space:]]*"github:' flake.nix)
[ "$input_count" -eq 2 ] || { echo "expected only pinned Nixpkgs and Luafun inputs; found $input_count" >&2; exit 1; }
grep -Fq 'nixpkgs.url = "github:NixOS/nixpkgs/' flake.nix
grep -Fq 'github:luafun/luafun/02960048e4dff4f5fd5b683c4b61f9df42e8339f' flake.nix
! grep -Eiq 'acornprover|acornlib|xds-agda|xdsAgda|miniVehicle|vehicle-formalisation' flake.nix || {
  echo "unexpected auxiliary prover/semantics dependency in flake.nix" >&2
  exit 1
}

# The repository-wide CI profile is an explicit, validated input.
grep -Fxq 'profile=all' .ci/global.txt || {
  echo "expected profile=all in .ci/global.txt" >&2
  exit 1
}

# Fennel-synced monolith options prefer lossy unification over auto-inline.
for monolith in FullCoupled/CanonicalLearnerMonolith.agda FullCoupled/TheoremsMonolith.agda; do
  grep -Fxq -- '--lossy-unification' <(sed -n '1,/^#-}/p' "$monolith") || {
    echo "expected --lossy-unification in $monolith options" >&2
    exit 1
  }
  ! grep -Fxq -- '--auto-inline' <(sed -n '1,/^#-}/p' "$monolith") || {
    echo "obsolete --auto-inline option remains in $monolith" >&2
    exit 1
  }
done

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

# The monoliths deliberately opt into --with-K. Enforce this project's
# non-cubical source path; this does not characterize all possible Agda setups.
for monolith in FullCoupled/CanonicalLearnerMonolith.agda FullCoupled/TheoremsMonolith.agda; do
  grep -Fq -- '--with-K' "$monolith" || {
    echo "expected --with-K option in $monolith" >&2
    exit 1
  }
  ! grep -Eq '^[[:space:]]*--cubical(=|$)' "$monolith" || {
    echo "Cubical mode conflicts with selected --with-K path: $monolith" >&2
    exit 1
  }
  ! grep -Eq '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Cubical([.]|[[:space:]]|$)' "$monolith" || {
    echo "direct Cubical import is not permitted in selected --with-K path: $monolith" >&2
    exit 1
  }
done
! grep -Fq 'GuardedCubical' FullCoupled/TheoremsMonolith.agda
! grep -Fq 'cubical=no-glue' FullCoupled/TheoremsMonolith.agda

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
# Fixed-hash ccforth plus Nixpkgs Forth, documentation, and Scheme tools.
grep -Fq 'ccforth = system:' flake.nix
grep -Fq 'ccforth_0.3.2_linux_amd64.tar.gz' flake.nix
grep -Fq 'ccforth_0.3.2_linux_arm64.tar.gz' flake.nix
grep -Fq 'ccforth_0.3.2_darwin_amd64.tar.gz' flake.nix
grep -Fq 'ccforth_0.3.2_darwin_arm64.tar.gz' flake.nix
grep -Fq 'pkgs.gforth' flake.nix
grep -Fq 'pkgs.groff' flake.nix
grep -Fq 'pkgs.guile' flake.nix
grep -Fq 'forth = pkgs.mkShell' flake.nix
grep -Fq 'name = "scott-strachey-domain-check";' flake.nix
grep -Fq 'name = "monoid-lstm-stream-check";' flake.nix
echo 'official-nix-surface=pass'
