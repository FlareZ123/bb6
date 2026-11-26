#!/usr/bin/env bash
# Build the complete A0RD and A1RB family bounds and their local roster consumer.
# LEAN_DEPS must point at Canonical77 artifact 14997966221 or its coherent rebuild.
set -euo pipefail
cd "$(dirname "$0")"
root="$PWD"
: "${LEAN_DEPS:?set LEAN_DEPS to the coherent original Canonical77 dependency directory}"
export LEAN_DEPS="$(realpath "$LEAN_DEPS")"
export LEAN="${LEAN:-lean}"
export WORKERS="${WORKERS:-4}"
export LEAN_PATH="$root:$LEAN_DEPS"
"$LEAN" --version
check() { local f="$1"; "$LEAN" -j1 -o "${f%.lean}.olean" "$f"; }
for m in CanonicalPartial Raw40Nores Raw40Pump Raw40MorePumps Raw40MoreTwoSided Raw40BinaryCarry Raw40Round38Nested Raw40Round39Nested Raw40Round42NestedRB Raw40Round43NestedRB Raw40FamilyFilterBase Raw40LocalCut Raw40A0RDBase Raw40A1RBBase; do
    check "$m.lean"
done
cp ../agent46-raw13-cut/Agent46AutoPump.lean Agent46AutoPump.lean
check Agent46AutoPump.lean
dirs=()
for c in 0LC 0LE 0RC 0RE 1LB 1LC 1LE 1RC 1RE; do
    python3 prepare_a0rd.py "$c"
    case "$c" in
        0LE) dirs+=("$root/round38/shards-input/shards"); check Raw40Round38Pump.lean;;
        1LB) dirs+=("$root/round39/shards-input/shards"); check Raw40Round39Pump.lean;;
        1LE) dirs+=("$root/round40/shards-input/shards"); check Raw40Round40Pump.lean;;
        1RE) dirs+=("$root/round41/shards-input/shards"); check Raw40Round41Pump.lean;;
        *) dirs+=("$root/a0rd/$c/shards");;
    esac
done
for c in 0LA 0LC 0LE 0RC 0RE 1LB 1LC 1LE 1RC 1RE; do
    python3 prepare_a1rb.py "$c"
    dirs+=("$root/a1rb/$c/shards")
    case "$c" in 0LE|1LB|1LE|1RE) check "Raw40RB${c}Pump.lean";; esac
done
python3 build_manifests.py "${dirs[@]}"
for d in "${dirs[@]}"; do export LEAN_PATH="$LEAN_PATH:$d"; done
for m in Raw40Round38Exact Raw40Round39Exact Raw40Round40Exact Raw40Round41Exact Raw40RB0LEExact Raw40RB0REExact Raw40RB1LBExact Raw40RB1LEExact Raw40RB1REExact Raw40A0RD Raw40A1RB Raw40RDRefine Raw40FamilyRefineBase Raw40FamilyRefine; do
    check "$m.lean"
done
