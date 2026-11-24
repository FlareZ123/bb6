#!/usr/bin/env bash
set -euo pipefail
: "${BATCH_RANGES:?Set comma-separated offset:size:fuel ranges}"
[[ "$BATCH_RANGES" =~ ^(0|[1-9][0-9]{0,4}):[1-9][0-9]{0,4}:(0|[1-9][0-9]{0,6})(,(0|[1-9][0-9]{0,4}):[1-9][0-9]{0,4}:(0|[1-9][0-9]{0,6})){0,7}$ ]]
IFS=, read -ra ranges <<< "$BATCH_RANGES"
for range in "${ranges[@]}"; do
  IFS=: read -r offset size fuel <<< "$range"
  (( offset < 12820 && size <= 12820 - offset && fuel <= 1000000 ))
done
mkdir -p agent8-batch
printf 'offset\tsize\tfuel\tstatus\n' > agent8-batch/manifest.tsv
git rev-parse HEAD > agent8-batch/original-revision.txt
printf '%s\n' "${GITHUB_SHA:-local}" > agent8-batch/research-revision.txt
failed=0
for range in "${ranges[@]}"; do
  IFS=: read -r offset size fuel <<< "$range"
  module="Agent8Batch_${offset}_${size}_${fuel}"
  cat > "$module.v" <<COQ
From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint Agent8PackedRoot.
From Coq Require Import List NArith Strings.String.
Import ListNotations.
Import TNF_Node.
Open Scope string_scope.
Definition chunk_input := q_i $offset $size.
Definition chunk_fuel : N := $fuel%N.
Time Definition chunk_data := Eval vm_compute in
  encode_queue (SearchQueue_upds decider chunk_input chunk_fuel).
Theorem chunk_data_exact :
  SearchQueue_upds decider chunk_input chunk_fuel = decode_queue chunk_data.
Proof.
  apply source_checkpoint_decode.
  - apply checkpoint_chunk_canonical.
  - Time vm_compute. reflexivity.
Qed.
Print Assumptions chunk_data_exact.
Time Eval vm_compute in (List.length (fst chunk_data), List.length (snd chunk_data)).
Set Printing Depth 100000.
Set Printing Width 120.
Print chunk_data.
COQ
  cp "$module.v" agent8-batch/
  if timeout 180s coqc -Q . BusyCoq -native-compiler no "$module.v" > "agent8-batch/$module.log" 2>&1; then
    cp "$module.vo" agent8-batch/
    printf '%s\t%s\t%s\tverified\n' "$offset" "$size" "$fuel" >> agent8-batch/manifest.tsv
    echo "$module verified"
    grep -E 'Finished transaction|= \([0-9]+, [0-9]+\)' "agent8-batch/$module.log" || true
  else
    status=$?
    printf '%s\t%s\t%s\tfailed:%s\n' "$offset" "$size" "$fuel" "$status" >> agent8-batch/manifest.tsv
    echo "$module failed with $status"
    tail -n 12 "agent8-batch/$module.log"
    failed=1
  fi
done
exit "$failed"
