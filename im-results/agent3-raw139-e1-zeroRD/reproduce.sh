#!/usr/bin/env bash
# Reproduce the exact D0=0RE cylinder without performing any new discovery.
# Run from repository root, with Lean 4.36.0-rc2 and the extracted accepted
# OneLB C1=0RA dependency artifact 15175093456.
set -euo pipefail
base="$PWD/im-results/agent3-raw139-e1-zeroRD"
work="$(realpath -m "${1:-.tmp/a3-e1-zeroRD}")"
core="$(realpath "$2")"
mkdir -p "$work"
export PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA"
g++ -std=c++17 -O3 im-results/agent48-raw139-e0-0re/replay.cpp -o "$work/replay"
"$work/replay" 450 2 7 24 11 24 14 24 17 16 24 13 24 24 > "$work/partition.json"
echo "3d69cf3e91812cebf72213a743adbf463e7d0bfd8733092ccaec1bc06315b2a6  $work/partition.json" | sha256sum -c -
python3 "$base/emit.py" "$work/partition.json" "$base/recipes.json" "$work/src" 600
python3 "$base/compile.py" "$work/src" "$core" "$(command -v lean)"
export LEAN_PATH="$core:$work/src"
lean -j 1 "$base/Restart.lean"
lean -j 1 "$base/Attain.lean"
