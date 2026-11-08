#!/usr/bin/env bash
# Regenerate the static dependency-graph images (dependency_graph.svg / .png)
# that are embedded in the top-level README.
#
# These are a snapshot of the interactive blueprint graph, rendered so they show
# up on GitHub (which cannot run the WASM-based live graph). Re-run this whenever
# the blueprint dependencies in src/content.tex change.
#
# Requirements:
#   * `leanblueprint web` has been run (produces web/dep_graph_document.html),
#   * Graphviz (`dot`, using the engine specified in the graph page),
#   * python3 with cairosvg and the Cairo system library (rasterizes svg -> png).
set -euo pipefail
cd "$(dirname "$0")"

HTML="web/dep_graph_document.html"
[ -f "$HTML" ] || { echo "Missing $HTML — run 'leanblueprint web' first."; exit 1; }

# Help Python find Homebrew's Cairo library on macOS.
if [[ "$(uname -s)" == Darwin ]] && command -v brew >/dev/null 2>&1; then
  export DYLD_FALLBACK_LIBRARY_PATH="$(brew --prefix)/lib${DYLD_FALLBACK_LIBRARY_PATH:+:$DYLD_FALLBACK_LIBRARY_PATH}"
fi
python3 -c 'import cairosvg'
command -v dot >/dev/null 2>&1 || { echo "Graphviz (dot) is required." >&2; exit 1; }

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# 1. Extract the graphviz `dot` source embedded in the generated graph page,
#    and give it a white background so it is legible in GitHub light & dark mode.
python3 - "$HTML" "$tmp/dep.dot" "$tmp/engine" <<'PY'
import re, sys
from pathlib import Path

html = Path(sys.argv[1]).read_text(encoding="utf-8")
m = re.search(r'renderDot\(`(.*?)`\)', html, re.S)
if m is None:
    raise SystemExit(f"No embedded dependency graph found in {sys.argv[1]}")
dot = m.group(1).replace('\\n', '\n').replace('bgcolor=transparent', 'bgcolor=white')
Path(sys.argv[2]).write_text(dot, encoding="utf-8")
engine = re.search(r'\.engine\("([^"]+)"\)', html)
Path(sys.argv[3]).write_text(engine.group(1) if engine else 'dot', encoding="utf-8")
PY

# 2. dot -> svg with the installed Graphviz. The compact graph uses nop2
# to preserve its fixed section positions; the wide graph uses dot.
# Rendering is entirely local and does not install dependencies.
graph_engine="$(cat "$tmp/engine")"
dot -K"$graph_engine" -Tsvg "$tmp/dep.dot" -o "$tmp/svg.svg"

# 3. svg -> png (2x) for the most robust GitHub rendering.
python3 - "$tmp/svg.svg" "$tmp/graph.png" <<'PY'
import cairosvg
import sys

cairosvg.svg2png(url=sys.argv[1], write_to=sys.argv[2],
                 scale=2.0, background_color="white")
PY

# Update the committed images only after both rendering steps succeed.
cp "$tmp/svg.svg" dependency_graph.svg
cp "$tmp/graph.png" dependency_graph.png

echo "Wrote dependency_graph.svg and dependency_graph.png"
