#!/usr/bin/env bash
# Check the Lean declaration names emitted by `leanblueprint web`.
set -euo pipefail
cd "$(dirname "$0")/.."

if [ ! -s blueprint/lean_decls ]; then
  echo "Missing blueprint/lean_decls — run 'leanblueprint web' first." >&2
  exit 1
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

{
  echo 'import GaussianTesting'
  while IFS= read -r decl || [ -n "$decl" ]; do
    [ -z "$decl" ] || printf '#check %s\n' "$decl"
  done < blueprint/lean_decls
} > "$tmp/CheckDecls.lean"

lake env lean "$tmp/CheckDecls.lean"
