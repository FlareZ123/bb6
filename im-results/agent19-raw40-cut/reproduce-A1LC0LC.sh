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
for m in CanonicalPartial Raw40Nores Raw40A1LC0LCPeriodic; do check "$m.lean"; done
(cd ../agent32-raw59; "$LEAN" -j1 -o "$root/FastBiDFA.olean" FastBiDFA.lean)
python3 prepare_a1lc_0lc.py
for f in Raw40A1LC0LCCompact*.lean; do check "$f"; done
python3 build_manifests.py "$root/a1lc/0LC/shards"
export LEAN_PATH="$LEAN_PATH:$root/a1lc/0LC/shards"
check Raw40A1LC0LCExact.lean
