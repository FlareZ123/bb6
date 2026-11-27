#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to accepted Canonical77 dependencies (artifact 14997966221)}"
export LEAN_DEPS="$(realpath "$LEAN_DEPS")"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
export LEAN_PATH="$root:$LEAN_DEPS"
"$LEAN" --version
check() { local f="$1"; "$LEAN" -j1 -o "${f%.lean}.olean" "$f"; }
for m in CanonicalPartial Raw40Nores Raw40A1LC0LCPeriodic Raw40A1LC0RCLeaf88; do check "$m.lean"; done
(cd ../agent32-raw59; "$LEAN" -j1 -o "$root/FastBiDFA.olean" FastBiDFA.lean)
dirs=()
for c in 0LC 0RC 1LB 1RC 1LE; do
  python3 prepare_a1lc_0lc.py "$c"
  for f in Raw40A1LC"${c}"Compact*.lean; do check "$f"; done
  dirs+=("$root/a1lc/$c/shards")
done
python3 build_manifests.py "${dirs[@]}"
for d in "${dirs[@]}"; do export LEAN_PATH="$LEAN_PATH:$d"; done
for c in 0LC 0RC 1LB 1RC 1LE; do check "Raw40A1LC${c}Exact.lean"; done
