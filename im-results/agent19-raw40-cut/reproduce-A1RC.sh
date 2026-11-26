#!/usr/bin/env bash
# Rebuild the A1=1RC branch proof with the original Canonical77 dependencies.
# Usage: LEAN_DEPS=/absolute/path/to/extracted/olean-directory bash reproduce-A1RC.sh
# Use Lean 4.36.0-rc2 and coherent artifact 14997966221 (run 45554648116),
# or rebuild those dependencies from their original pinned source closure.
set -euo pipefail
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to the extracted coherent dependency directory}"
export LEAN_PATH="$root:$LEAN_DEPS"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
"$LEAN" --version
check() {
    local f="$1"
    "$LEAN" -j1 -o "${f%.lean}.olean" "$f"
}
check CanonicalPartial.lean
check Raw40Nores.lean
cp ../agent46-raw13-cut/Agent46AutoPump.lean Agent46AutoPump.lean
cmp ../agent46-raw13-cut/Agent46AutoPump.lean Agent46AutoPump.lean
check Agent46AutoPump.lean
for f in Raw40Leaf236 Raw40NestedCore Raw40PairCore Raw40AffineCore Raw40DigitCore Raw40Triple32 Raw40CarryCore Raw40CarryLeaves Raw40Grow320 Raw40Quint745; do
    check "$f.lean"
done
python3 prepare_round21.py
python3 prepare_round22_23.py 22
python3 prepare_round22_23.py 23
python3 prepare_round24_25.py 24
python3 prepare_round24_25.py 25
for f in Raw40NestedLeaves Raw40PairLeaves Raw40AffineLeaves; do check "$f.lean"; done
codes=(0LB 1LC 1LD 0LD 0RC)
for n in 21 22 23 24 25; do
    check "Raw40Round${n}Pump.lean"
    m="Raw40C1RC${codes[$((n-21))]}"
    d="$root/round${n}/shards-input/shards"
    export LEAN_PATH="$LEAN_PATH:$d"
    (cd "$d"; check "${m}Base.lean"; for f in "${m}"Kid*.lean; do check "$f"; done; check "${m}All.lean")
    check "Raw40Round${n}Exact.lean"
done
for n in 26 27 28 29; do python3 prepare_round26_29.py "$n"; done
check Raw40DigitLeaves.lean
for n in 30 31 32 33 34; do python3 prepare_round30_34.py "$n"; done
for f in Raw40Sibling30Pump Raw40Sibling31Pump Raw40OneRC1LB; do check "$f.lean"; done
# Existing DAG builder uses root/deps.
if [ ! -e deps ]; then ln -s "$LEAN_DEPS" deps; fi
python3 build_modular.py 26 27 28 29 30 31 32 33 34
for n in 26 27 28 29 30 31 32 33 34; do
    export LEAN_PATH="$LEAN_PATH:$root/round${n}/shards-input/shards"
done
check Raw40A1RCBase.lean
check Raw40A1RC.lean
