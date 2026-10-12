#!/usr/bin/env bash
set -euo pipefail

dot_file="${1:?Agda dependency graph DOT file}"
output_manifest="${2:?output source manifest}"
root_source="${3:?root Agda source file}"
shift 3
roots=("$@")

test -s "$dot_file"
test -s "$root_source"
test "${#roots[@]}" -gt 0

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

declare -A module_files=()

add_source() {
  local file="$1"
  local module
  module=$(awk '/^[[:space:]]*module[[:space:]]+/ { print $2; exit }' "$file")
  if [ -n "$module" ] && [ -z "${module_files[$module]+x}" ]; then
    module_files["$module"]="$file"
  fi
}

add_source "$root_source"

while IFS= read -r -d '' file; do
  add_source "$PWD/$file"
done < <(git -C "$PWD" ls-files -z '*.agda' '*.lagda')

for root in "${roots[@]}"; do
  test -d "$root"
  if git -C "$root" rev-parse --show-toplevel >/dev/null 2>&1; then
    while IFS= read -r -d '' file; do
      add_source "$root/$file"
    done < <(git -C "$root" ls-files -z '*.agda' '*.lagda')
  else
    while IFS= read -r -d '' file; do
      add_source "$file"
    done < <(find "$root" -type f \( -name '*.agda' -o -name '*.lagda' \) -print0)
  fi
done

: > "$tmp/modules"
sed -n 's/.*"\([^"]*\)".*/\1/p' "$dot_file" | sort -u > "$tmp/modules"

: > "$output_manifest"
root_module=$(awk '/^[[:space:]]*module[[:space:]]+/ { print $2; exit }' "$root_source")
[ -n "$root_module" ] || { echo "cannot determine root module name" >&2; exit 1; }
printf '%s\n' "${module_files[$root_module]}" >> "$output_manifest"

# Legacy sources are inventoried as text only, not included in the kernel-checked closure.
while IFS= read -r -d '' file; do
  printf '%s\n' "$PWD/$file" >> "$output_manifest"
done < <(git -C "$PWD" ls-files -z '*.agda' '*.lagda')

unresolved=0
while IFS= read -r module; do
  [ -n "$module" ] || continue
  if [ -n "${module_files[$module]+x}" ]; then
    printf '%s\n' "${module_files[$module]}" >> "$output_manifest"
  else
    unresolved=$((unresolved + 1))
  fi
done < "$tmp/modules"

sort -u -o "$output_manifest" "$output_manifest"
test -s "$output_manifest"

printf 'agda-semantic-source-inventory=pass\n'
printf 'resolved-source-count=%s\n' "$(wc -l < "$output_manifest")"
printf 'unresolved-dot-symbol-count=%s\n' "$unresolved"
