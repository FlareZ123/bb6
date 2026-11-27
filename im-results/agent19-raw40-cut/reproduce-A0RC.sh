#!/usr/bin/env bash
# Rebuild the full A1=0RC family using coherent Canonical77 dependencies.
set -euo pipefail
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to the coherent Canonical77 dependency directory (artifact 14997966221)}"
export LEAN_DEPS="$(realpath "$LEAN_DEPS")"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
export LEAN_PATH="$root:$LEAN_DEPS"
"$LEAN" --version
check() { local m="$1"; "$LEAN" -j1 -o "$m.olean" "$m.lean"; }
for m in CanonicalPartial Raw40Nores Raw40Pump Raw40MorePumps Raw40LocalCut Raw40FamilyFilterBase Raw40A0RCBase; do check "$m"; done
(cd ../agent32-raw59; "$LEAN" -j1 -o "$root/FastBiDFA.olean" FastBiDFA.lean)
dirs=()
for c in 0LA 0LB 0LE 0RB 0RD 0RE 1LA 1LB 1LC 1LE 1RB 1RD 1RE; do
    python3 prepare_a0rc.py "$c"
    d="$root/a0rc/$c/shards"
    dirs+=("$d")
    for m in $(cat "$root/a0rc/$c/imports.txt"); do check "$m"; done
done
python3 build_manifests.py "${dirs[@]}"
for d in "${dirs[@]}"; do export LEAN_PATH="$LEAN_PATH:$d"; done
for c in 0LA 0LB 0LE 0RB 0RD 0RE 1LA 1LB 1LC 1LE 1RB 1RD 1RE; do
    (cd "a0rc/$c/shards"; check "Raw40C0RC${c}Exact")
done
check Raw40A0RC
check Raw40RCRefine
