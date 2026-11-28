#!/usr/bin/env bash
# Kernel-proof pipeline for the source-connected F197 blank-root theorem.
# Run only in the existing manual GitHub Actions workflow.
set -euo pipefail
mode="${1:?expected base, shard, or final}"
shard="${2:-0}"
repo="$PWD"
e="$repo/im-results/agent2-f197-sweep"
d="$repo/im-results/agent31-f197-macro"
b="$RUNNER_TEMP/f197-par-work"
mkdir -p "$b"

if [[ "$mode" == base ]]; then
  python3 "$e/generate_lean_trace.py" "$b"
  python3 "$e/generate_packed_banks.py" "$b"
  python3 "$e/generate_root_trace.py" "$b"
  cp "$d/Macro.lean" "$b/"
  for m in PrefixCheck EpochMarker EpochMarkerExit EpochEntrance EpochMarkerBulk CounterCore SelfBase OrdinaryCore OrdinaryBulk TraceLogic PackedCheck SeedCore RootCore; do
    cp "$e/$m.lean" "$b/"
  done
  cd "$b"
  export LEAN_PATH=.
  for m in Macro PrefixCheck EpochMarker EpochMarkerExit EpochEntrance EpochMarkerBulk CounterCore SelfBase OrdinaryCore OrdinaryData OrdinaryBulk TraceLogic PackedCheck SeedCore RootCore TraceStates; do
    lean -j 1 -o "$m.olean" "$m.lean"
  done
  compile() {
    local s="$1"
    lean -j 1 -o "${s%.lean}.olean" "$s"
  }
  export -f compile
  printf '%s\n' OpBank*.lean | xargs -P 2 -n 1 bash -eo pipefail -c 'compile "$0"'
  printf '%s\n' SelfPre*.lean SelfPost*.lean | xargs -P 2 -n 1 bash -eo pipefail -c 'compile "$0"'
  lean -j 1 -o SelfTheorem.olean SelfTheorem.lean
  lean -j 1 -o RootStates.olean RootStates.lean
  printf '%s\n' RootBank*.lean | xargs -P 2 -n 1 bash -eo pipefail -c 'compile "$0"'
  tar -czf "$RUNNER_TEMP/f197-par-base.tar.gz" -C "$b" .
  echo "Source base complete"
elif [[ "$mode" == shard ]]; then
  [[ "$shard" =~ ^[0-3]$ ]] || exit 2
  tar -xzf "$RUNNER_TEMP/f197-par-download/f197-par-base.tar.gz" -C "$b"
  cd "$b"
  export LEAN_PATH=.
  count=0
  for part in RootPart*.lean; do
    n="${part#RootPart}"
    n="${n%.lean}"
    if (( n % 4 == shard )); then
      lean -j 1 -o "${part%.lean}.olean" "$part"
      count=$((count+1))
    fi
  done
  echo "Certified shard $shard: $count RootPart modules"
  test "$count" -gt 0
  tar -czf "$RUNNER_TEMP/f197-par-part-$shard.tar.gz" RootPart*.olean
elif [[ "$mode" == final ]]; then
  tar -xzf "$RUNNER_TEMP/f197-par-download/f197-par-base.tar.gz" -C "$b"
  for k in 0 1 2 3; do
    tar -xzf "$RUNNER_TEMP/f197-par-download/f197-par-part-$k.tar.gz" -C "$b"
  done
  cp im-results/agent8-coverage-contract/{Frontier,Symmetry,RootShift}.lean "$b/"
  cp im-results/agent42-coverage-normal/FirstStep.lean "$b/"
  cp im-results/agent4-coverage-smoke/WriteOneDrift.lean "$b/"
  cp im-results/agent13-weighted-first-one/{BlankDelayKernel,BlankDelaySource,SparseBlankDelay}.lean "$b/"
  cp im-results/agent31-f197-macro/{CoverBridge,F197WeightedLeaf}.lean "$b/"
  cp im-results/agent2-f197-sweep/F197BlankCover.lean "$b/"
  cd "$b"
  export LEAN_PATH=.
  lean -j 1 -o RootTheorem.olean RootTheorem.lean | tee "$RUNNER_TEMP/f197-root-axioms.log"
  for m in Frontier Symmetry RootShift FirstStep WriteOneDrift BlankDelayKernel BlankDelaySource SparseBlankDelay CoverBridge F197WeightedLeaf F197BlankCover; do
    lean -j 1 -o "$m.olean" "$m.lean" | tee -a "$RUNNER_TEMP/f197-root-axioms.log"
  done
  ! grep -q sorryAx "$RUNNER_TEMP/f197-root-axioms.log"
  tar -czf "$RUNNER_TEMP/f197-par-complete.tar.gz" RootTheorem.olean F197BlankCover.olean
else
  echo "Unknown mode: $mode" >&2
  exit 2
fi
