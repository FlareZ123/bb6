#!/usr/bin/env bash
set -euo pipefail
# Input: existing exact original-source packed checkpoints. The output
# is a kernel-checked continuation, including every residual active/held node.
mkdir -p fast-old fast-results
gh run download 45608313328 --repo FlareZ123/bb6 --pattern 'phase-consumption-*' --dir fast-old
# GH creates an artifact-named subdirectory for pattern downloads.
old_dir=$(dirname "$(find fast-old -name verified.tsv -print -quit)")
[[ -f "$old_dir/verified.tsv" ]]
[[ "$FAST_OFFSETS" =~ ^[0-9]+(,[0-9]+)*$ ]]
[[ "$FAST_FUEL" =~ ^[0-9]+$ ]]
(( FAST_FUEL >= 1 && FAST_FUEL <= 1000000 ))
printf 'offset\told_fuel\tfast_fuel\tnew_active\tnew_held\tmodule\n' > fast-results/verified.tsv
IFS=, read -r -a offsets <<< "$FAST_OFFSETS"
for offset in "${offsets[@]}"; do
  row=$(awk -F '\t' -v o="$offset" 'NR>1 && $1==o {print; exit}' "$old_dir/verified.tsv")
  [[ -n "$row" ]] || { echo "missing exact checkpoint $offset"; exit 1; }
  IFS=$'\t' read -r offset size oldfuel active held ac hc module <<< "$row"
  [[ "$module" =~ ^Agent8Batch_[0-9]+_[0-9]+_[0-9]+$ ]]
  cp "$old_dir/$module.v" "$old_dir/$module.vo" .
  name="Agent5FastResume_${offset}_${FAST_FUEL}"
  cat > "$name.v" <<COQ
From BusyCoq Require Import Enumerate62 Agent8QueueCheckpoint Agent8WeightedSource
  Agent32SourceBackwards Agent5FastSource ${module}.
From Coq Require Import List NArith Strings.String.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.
Time Definition fast_packed : packed_queue := Eval vm_compute in
  (encode_queue (SearchQueue_upds fast_decider
    (decode_queue ${module}.chunk_data) ${FAST_FUEL}%N)).
Theorem fast_packed_exact :
  encode_queue (SearchQueue_upds fast_decider
    (decode_queue ${module}.chunk_data) ${FAST_FUEL}%N) = fast_packed.
Proof. Time vm_compute. reflexivity. Qed.
Theorem fast_queue_exact :
  SearchQueue_upds fast_decider (decode_queue ${module}.chunk_data) ${FAST_FUEL}%N =
  decode_queue fast_packed.
Proof. apply source_checkpoint_decode; [apply checkpoint_decode_canonical|exact fast_packed_exact]. Qed.
Theorem fast_source_covered bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  safeQ (source_weighted_safe bound) (decode_queue fast_packed) ->
  safeQ (source_weighted_safe bound) (q_i ${offset} ${size}).
Proof.
  intros HB H.
  eapply fast_checkpoint_resume; [exact HB|exact ${module}.chunk_data_exact|exact fast_queue_exact|exact H].
Qed.
Print Assumptions fast_source_covered.
Eval vm_compute in (List.length (fst fast_packed), List.length (snd fast_packed)).
Set Printing Depth 1000000.
Set Printing Width 200.
Print fast_packed.
COQ
  # Exact checkpoint module object is already certified. Read its source
  # names from the canonical exporter, and fail closed if they differ.
  grep -q 'Definition chunk_data ' "$module.v" || { cat "$module.v"; exit 1; }
  if ! timeout 300s coqc -Q . BusyCoq -native-compiler no "$name.v" > "fast-results/$name.log" 2>&1; then
    tail -n 40 "fast-results/$name.log"
    exit 1
  fi
  cp "$name.v" "$name.vo" "$module.v" "$module.vo" fast-results/
  counts=$(python3 -c 'import re,sys; s=open(sys.argv[1]).read(); m=re.findall(r"=\s*\((\d+),\s*(\d+)\)\s*:\s*nat\s*\*\s*nat",s); assert m, s[-1000:]; print("\t".join(m[-1]))' "fast-results/$name.log")
  printf '%s\t%s\t%s\t%s\t%s\n' "$offset" "$oldfuel" "$FAST_FUEL" "$counts" "$name" >> fast-results/verified.tsv
done
cat fast-results/verified.tsv
counts=$(awk -F '\t' 'NR>1 {a+=$4; h+=$5; n++} END {printf "%dchunks-%dactive-%dheld",n,a,h}' fast-results/verified.tsv)
echo "summary=$counts" >> "$GITHUB_OUTPUT"
