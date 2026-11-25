#!/usr/bin/env bash
set -euo pipefail
mkdir -p coarse-results coarse-checkpoint
gh run download 45522264094 --repo FlareZ123/bb6 --name source-packed-chunk --dir coarse-checkpoint
cp coarse-checkpoint/Agent8PackedChunk.{v,vo} .
cp "$GITHUB_WORKSPACE/research/im-results/agent5-weighted-tnf-queue/"Agent5CoarseConsume*.v .
cp Agent5CoarseTree.{v,vo} coarse-results/
IFS=, read -ra shards <<< "$COARSE_SHARDS"
failed=0
for shard in "${shards[@]}"; do
  case "$shard" in Small|A|B|C|D) ;; *) echo "Unknown shard $shard"; exit 2;; esac
  if ! timeout 300s coqc -Q . BusyCoq -native-compiler no "Agent5Coarse$shard.v" > "coarse-results/shard-$shard.log" 2>&1; then
    tail -n 100 "coarse-results/shard-$shard.log"; failed=1; continue
  fi
  cp "Agent5Coarse$shard."{v,vo} coarse-results/
  if ! timeout 300s coqc -Q . BusyCoq -native-compiler no "Agent5CoarseConsume$shard.v" > "coarse-results/consume-$shard.log" 2>&1; then
    if grep -Eqi 'inconsistent assumptions|bad magic number|compiled library|cannot load' "coarse-results/consume-$shard.log"; then
      timeout 600s coqc -Q . BusyCoq -native-compiler no Agent8PackedChunk.v > coarse-results/checkpoint-rebuild.log 2>&1
      if ! timeout 300s coqc -Q . BusyCoq -native-compiler no "Agent5CoarseConsume$shard.v" >> "coarse-results/consume-$shard.log" 2>&1; then failed=1; continue; fi
    else tail -n 100 "coarse-results/consume-$shard.log"; failed=1; continue; fi
  fi
  cp "Agent5CoarseConsume$shard."{v,vo} coarse-results/
  cat "coarse-results/consume-$shard.log"
done
if [[ -f Agent5CoarseSmall.vo && -f Agent5CoarseA.vo && -f Agent5CoarseB.vo && -f Agent5CoarseC.vo && -f Agent5CoarseD.vo ]]; then
  if timeout 300s coqc -Q . BusyCoq -native-compiler no Agent5CoarseConsumeAll.v > coarse-results/consume-All.log 2>&1; then
    cp Agent5CoarseConsumeAll.{v,vo} coarse-results/
    cat coarse-results/consume-All.log
  else tail -n 100 coarse-results/consume-All.log; failed=1; fi
fi
exit "$failed"
