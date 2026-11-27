#!/usr/bin/env bash
# Rebuild all ten A1=0LB children and their exact weighted maximum.
set -euo pipefail
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to the coherent Canonical77 dependency directory (artifact 14997966221)}"
export LEAN_DEPS="$(realpath "$LEAN_DEPS")"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
export LEAN_PATH="$root:$LEAN_DEPS"
"$LEAN" --version
check() { local f="$1"; "$LEAN" -j1 -o "${f%.lean}.olean" "$f"; }
for m in CanonicalPartial Raw40Nores Raw40A0LBBase; do check "$m.lean"; done
cp ../agent46-raw13-cut/Agent46AutoPump.lean Agent46AutoPump.lean
check Agent46AutoPump.lean
(cd ../agent32-raw59; "$LEAN" -j1 -o "$root/FastBiDFA.olean" FastBiDFA.lean)
dirs=()
for c in 0LC 0LE 0RC 0RE 1LB 1LC 1LE 1RB 1RC 1RE; do
    python3 prepare_a0lb.py "$c"
    d="$root/a0lb/$c/shards"
    dirs+=("$d")
    for m in $(cat "$root/a0lb/$c/imports.txt"); do check "$m.lean"; done
done
python3 build_manifests.py "${dirs[@]}"
for d in "${dirs[@]}"; do export LEAN_PATH="$LEAN_PATH:$d"; done
check Raw40A0LB.lean
