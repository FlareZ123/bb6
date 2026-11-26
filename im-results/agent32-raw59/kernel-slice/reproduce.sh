#!/usr/bin/env bash
set -euo pipefail
src="$(cd "$(dirname "$0")" && pwd)"
base="$(realpath "$1")"
producer="$(realpath "$2")"
work="$(realpath -m "$3")"
mkdir -p "$work"
cd "$work"
printf '%s  %s\n' b6997b8b530e59357bf8deabbc295f51f03b85567b99773b2fa91248ca3be235 "$base" 45a1fcc14767df503e0e5fc6cfe43a02aa51530a6c9d3773831888e482379ff4 "$producer" | sha256sum -c -
mkdir -p raw119 raw59-1lb
unzip -jo "$base" '*.olean' -d raw119
unzip -jo "$producer" '*.olean' -d raw59-1lb
cp "$src/KernelSlice.lean" "$src/BridgeConsumer.lean" .
export LEAN_SYSROOT="$(lean --print-prefix)"
export LEAN_PATH="$PWD/raw119"
lean -c KernelSlice.c KernelSlice.lean
leanc -O2 -o kernelslice KernelSlice.c
printf '%s\n' Std Frontier WeightedTNF TNFPilot BlockFAR2 > legacy-base.txt
printf '%s\n' BB6.Agent32Raw59LB1Block194.never BB6.Agent32Raw59LB1Block194.table > bridge-roots.txt
find "$PWD/raw59-1lb" -name '*.olean' -type f | sort > bridge-objects.txt
./kernelslice legacy-base.txt bridge-roots.txt bridge-objects.txt Raw59BridgeSlice A32Raw59BridgeSlice Raw59BridgeSlice.olean
LEAN_PATH="$PWD:$LEAN_PATH" lean -o BridgeConsumer.olean BridgeConsumer.lean
