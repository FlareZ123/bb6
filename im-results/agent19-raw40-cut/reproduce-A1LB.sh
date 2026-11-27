#!/usr/bin/env bash
set -euo pipefail
shopt -s nullglob
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to Canonical77 artifact 14997966221}"
export LEAN_DEPS="$(realpath "$LEAN_DEPS")"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
export LEAN_PATH="$root:$LEAN_DEPS"
"$LEAN" --version
check() { local f="$1"; "$LEAN" -j1 -o "${f%.lean}.olean" "$f"; }
for m in CanonicalPartial Raw40Nores; do check "$m.lean"; done
(cd ../agent32-raw59; "$LEAN" -j1 -o "$root/FastBiDFA.olean" FastBiDFA.lean)
dirs=()
cases=( "$@" )
if (( ${#cases[@]} == 0 )); then cases=(1RD 1LB 0RD 0LB); fi
for c in "${cases[@]}"; do
  python3 prepare_a1lb.py "$c"
  for f in Raw40A1LB"${c}"Late.lean Raw40A1LB"${c}"Compact*.lean; do [[ ! -f "$f" ]] || check "$f"; done
  dirs+=("$root/a1lb/$c/shards")
done
python3 build_manifests.py "${dirs[@]}"
for d in "${dirs[@]}"; do export LEAN_PATH="$LEAN_PATH:$d"; done
for c in "${cases[@]}"; do check "Raw40A1LB${c}Exact.lean"; done
if (( ${#cases[@]} == 16 )); then
  check Raw40A1LBBase.lean
  check Raw40A1LB.lean
fi
