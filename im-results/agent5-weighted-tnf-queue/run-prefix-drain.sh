#!/usr/bin/env bash
set -euo pipefail
# Independent small root slice, not an extrapolation from a 100-root checkpoint.
# The exact original classifier remains unchanged.
[[ "$DRAIN_RANGES" =~ ^[0-9]+:[0-9]+:[0-9]+(,[0-9]+:[0-9]+:[0-9]+)*$ ]]
IFS=, read -r -a ranges <<< "$DRAIN_RANGES"
mkdir -p prefix-results
printf 'offset\tsize\tfuel\tactive\theld\tmodule\n' > prefix-results/verified.tsv
for range in "${ranges[@]}"; do
  IFS=: read -r offset size fuel <<< "$range"
  (( offset < 12820 && size >= 1 && size <= 20 && fuel >= 1 && fuel <= 10000000 ))
  name="Agent5Prefix_${offset}_${size}_${fuel}"
  cat > "$name.v" <<COQ
From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint Agent8PackedRoot
  Agent8WeightedSource Agent32SourceBackwards.
From Coq Require Import List NArith Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.
Definition prefix_input := q_i $offset $size.
Definition prefix_fuel : N := $fuel%N.
Time Definition prefix_data : packed_queue := Eval vm_compute in
  encode_queue (SearchQueue_upds decider prefix_input prefix_fuel).
Theorem prefix_encoded :
  encode_queue (SearchQueue_upds decider prefix_input prefix_fuel) = prefix_data.
Proof. vm_cast_no_check (eq_refl prefix_data). Time Qed.
Theorem prefix_exact :
  SearchQueue_upds decider prefix_input prefix_fuel = decode_queue prefix_data.
Proof. apply source_checkpoint_decode; [apply checkpoint_chunk_canonical|exact prefix_encoded]. Qed.
Theorem prefix_safe bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  safeQ (source_weighted_safe bound) (decode_queue prefix_data) ->
  safeQ (source_weighted_safe bound) prefix_input.
Proof.
  intros HB H.
  apply (source_updates_backwards _ decider (source_weighted_local bound HB) _ prefix_fuel).
  rewrite prefix_exact. exact H.
Qed.
Print Assumptions prefix_safe.
Eval vm_compute in (length (fst prefix_data), length (snd prefix_data)).
Set Printing Depth 1000000.
Set Printing Width 160.
Print prefix_data.
COQ
  if timeout 1200s coqc -Q . BusyCoq -native-compiler no "$name.v" > "prefix-results/$name.log" 2>&1; then
    cp "$name.v" "$name.vo" prefix-results/
    counts=$(python3 -c 'import re,sys; s=open(sys.argv[1]).read(); m=re.findall(r"=\s*\((\d+),\s*(\d+)\)\s*:\s*nat\s*\*\s*nat",s); assert m, s[-1000:]; print("\t".join(m[-1]))' "prefix-results/$name.log")
    printf '%s\t%s\t%s\t%s\t%s\n' "$offset" "$size" "$fuel" "$counts" "$name" >> prefix-results/verified.tsv
    tail -n 3 "prefix-results/verified.tsv"
  else
    cp "$name.v" prefix-results/
    tail -n 30 "prefix-results/$name.log"
    exit 1
  fi
done
counts=$(awk -F '\t' 'NR>1 {a+=$4; h+=$5; n++} END {printf "%dchunks-%dactive-%dheld",n,a,h}' prefix-results/verified.tsv)
echo "summary=$counts" >> "$GITHUB_OUTPUT"
