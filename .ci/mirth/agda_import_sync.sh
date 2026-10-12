#!/usr/bin/env bash
set -euo pipefail

canonical=FullCoupled/CanonicalLearnerMonolith.agda
mode="${1:---check}"
block=$(mktemp)
merged=$(mktemp)
tmp=$(mktemp)
trap 'rm -f "$block" "$merged" "$tmp"' EXIT

sources() { git ls-files '*.agda' | LC_ALL=C sort; }
is_extraction_surface() {
  case "$1" in
    FullCoupled/Agda2HsSurface.agda|FullCoupled/Agda2HsSemanticExtractor.agda|FullCoupled/Agda2HsSemanticSearch.agda|FullCoupled/Agda2HsTheoremGraphEGraph.agda|FullCoupled/Agda2HsGraphSearchCheck.agda|FullCoupled/AgdaGraphShort.agda|FullCoupled/FormalMethods/IMP.agda|FullCoupled/FormalMethods/Types.agda|FullCoupled/FormalMethods/Security.agda|FullCoupled/FormalMethods/HoareLogic.agda|FullCoupled/FormalMethods/SeparationLogic.agda|FullCoupled/FormalMethods/OperationalSemantics.agda|FullCoupled/FormalMethods/VerificationConditions.agda|FullCoupled/FormalMethods/gentle-intro-to-reflection/tangled.agda)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}
common_sources() {
  while IFS= read -r file; do
    if ! is_extraction_surface "$file"; then
      printf '%s\n' "$file"
    fi
  done < <(sources)
}
extract_block() { sed -n '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/,/^-- END MIRTH-SYNC COMMON IMPORTS$/p' "$1"; }
canonical_imports() {
  extract_block "$canonical" |
    sed '1d' |
    sed '$d' |
    sed '/^-- Merged external import surface/d' |
    sed '/^open import Agda\.Builtin\.Reflection/d' |
    sed '/^open import Haskell\.Law\.Num\.Def/d' |
    sed '/^open import Haskell\.Law\.Num\.Int/d' |
    sed '/^open import Haskell\.Prelude\.Nat\.Properties/d' |
    sed '/^open import InfinitePigeon\.FinitePigeon/d'
}
collect_imports() {
  canonical_imports
  while IFS= read -r file; do
    awk '
      $0 == "-- BEGIN MIRTH-SYNC COMMON IMPORTS" { inside=1; next }
      $0 == "-- END MIRTH-SYNC COMMON IMPORTS" { inside=0; next }
      !inside && $0 ~ /^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+/ {
        line=$0
        if (line ~ /FullCoupled[.]/) next
        # Keep the TypeTopology MLTT.Plus import local; it must not enter the shared Agda2hs import closure.
        if (line ~ /^open import MLTT[.]Plus([[:space:]]|$)/) next
        # Keep TypeTopology accessibility proof-only; do not merge it into the Agda2hs import surface.
        if (line ~ /^open import Ordinals[.]Notions[[:space:]]+_<_([[:space:]]|$)/) next
        if (line ~ /TWA[.]Thesis[.]Chapter3[.](ClosenessSpaces|SearchableTypes)[[:space:]]+fe([[:space:]]|$)/) next
        if (line ~ /^open import (Agda[.]Builtin[.]Reflection|Haskell[.]Law[.]Num[.]Def|Haskell[.]Law[.]Num[.]Int|Haskell[.]Prelude[.]Nat[.]Properties|Unsafe[.]Haskell)([[:space:]]|$)/) next
        if (line ~ /^open import InfinitePigeon[.]FinitePigeon([[:space:]]|$)/) next
        # Keep the learner logical spec's MLTT and UF foundational imports module-local.
        if (line ~ /^open import (MLTT[.]Spartan|MLTT[.]Athenian|UF[.](Base|FunExt|PropTrunc|Size|Subsingletons|Subsingletons-FunExt|UA-FunExt|Equiv|SubtypeClassifier))([[:space:]]|$)/) next
        print line
      }
    ' "$file"
  done < <(common_sources)
}
normalized_block() {
  {
    printf '%s\n' '-- BEGIN MIRTH-SYNC COMMON IMPORTS'
    printf '%s\n' '-- Merged external import surface; internal FullCoupled imports remain module-local.'
    collect_imports | sed 's/[[:space:]]*$//' | sed '/^$/d' | LC_ALL=C sort -u
    printf '%s\n' '-- END MIRTH-SYNC COMMON IMPORTS'
  } > "$merged"
}
check_one() {
  file="$1"
  {
    echo '-- BEGIN MIRTH-SYNC COMMON IMPORTS'
    echo '-- Merged external import surface; internal FullCoupled imports remain module-local.'
    extract_block "$file" |
      sed '1d' |
      sed '$d' |
      sed '/^-- Merged external import surface/d' |
      sed 's/[[:space:]]*$//' |
      sed '/^$/d' |
      LC_ALL=C sort -u
    echo '-- END MIRTH-SYNC COMMON IMPORTS'
  } > "$block"
  cmp -s "$merged" "$block"
}
external_drift() {
  file="$1"
  awk '
    $0 == "-- BEGIN MIRTH-SYNC COMMON IMPORTS" { inside=1; next }
    $0 == "-- END MIRTH-SYNC COMMON IMPORTS" { inside=0; next }
    !inside && $0 ~ /^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+/ {
      mod=$0
      sub(/^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+/, "", mod)
      if (mod !~ /^FullCoupled[.]/ &&
          mod !~ /^MLTT[.]Plus([[:space:]]|$)/ &&
          mod !~ /^Ordinals[.]Notions[[:space:]]+_<_([[:space:]]|$)/ &&
          mod !~ /^TWA[.]Thesis[.]Chapter3[.](ClosenessSpaces|SearchableTypes)[[:space:]]+fe([[:space:]]|$)/ &&
          mod !~ /^Agda[.]Builtin[.]Reflection([[:space:]]|$)/ &&
          mod !~ /^Haskell[.]Law[.]Num[.](Def|Int)([[:space:]]|$)/ &&
          mod !~ /^Haskell[.]Prelude[.]Nat[.]Properties([[:space:]]|$)/ &&
          mod !~ /^InfinitePigeon[.]FinitePigeon([[:space:]]|$)/ &&
          mod !~ /^Unsafe[.]Haskell([[:space:]]|$)/ &&
          mod !~ /^MLTT[.](Spartan|Athenian)([[:space:]]|$)/ &&
          mod !~ /^UF[.](Base|FunExt|PropTrunc|Size|Subsingletons|Subsingletons-FunExt|UA-FunExt|Equiv|SubtypeClassifier)([[:space:]]|$)/)
        print FILENAME ": " $0
    }
  ' "$file"
}
rewrite_block() {
  file="$1"
  if grep -Fq -- '-- BEGIN MIRTH-SYNC COMMON IMPORTS' "$file"; then
    awk -v block="$merged" '
      $0 == "-- BEGIN MIRTH-SYNC COMMON IMPORTS" {
        while ((getline line < block) > 0) print line
        close(block); inside=1; next
      }
      $0 == "-- END MIRTH-SYNC COMMON IMPORTS" { inside=0; next }
      !inside { print }
    ' "$file" > "$tmp"
  else
    awk -v block="$merged" '
      /^module[[:space:]].*where[[:space:]]*$/ {
        print; print ""
        while ((getline line < block) > 0) print line
        close(block); print ""; next
      }
      { print }
    ' "$file" > "$tmp"
  fi
  mv "$tmp" "$file"
}
normalized_block
if [ "$mode" = "--check" ]; then
  failures=0
  while IFS= read -r file; do
    check_one "$file" || { echo "common import drift: $file" >&2; failures=$((failures + 1)); }
    if [ -n "$(external_drift "$file")" ]; then
      external_drift "$file" >&2
      failures=$((failures + 1))
    fi
  done < <(common_sources)
  test "$failures" -eq 0
elif [ "$mode" = "--write" ]; then
  while IFS= read -r file; do rewrite_block "$file"; done < <(common_sources)
  check_one "$canonical"
else
  echo 'usage: agda-import-sync [--check|--write]' >&2
  exit 2
fi
echo 'mirth-agda-import-sync=pass'
echo "canonical=$canonical"
echo "merged-external-imports=$(grep -Ec '^(open |import )' "$merged" || true)"
echo "sync-exceptions=Agda2Hs/* plus legacy FormalMethods/AgdaGraphShort mixed-import surfaces"