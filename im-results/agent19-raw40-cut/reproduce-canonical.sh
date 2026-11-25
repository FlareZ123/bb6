#!/bin/bash
# Run in this directory, after compiling the RDLC dependencies as documented.
set -euo pipefail
g++ -O3 -std=c++20 enumerate_canon.cpp -o enumerate_canon
g++ -O3 -std=c++20 farbank.cpp -o farbank
export LEAN_PATH="$LEAN_PATH:$PWD"
lean -o Raw40TwoSided.olean Raw40TwoSided.lean
lean -o Raw40MoreTwoSided.olean Raw40MoreTwoSided.lean
lean -o Raw40ThirdSweeps.olean Raw40ThirdSweeps.lean
lean -o Raw40Batch.olean Raw40Batch.lean
mkdir -p canon_batches
awk '{print $1,$2}' canonical-accepted.txt > canon_batches/inputs.txt
names=()
while read -r name table B; do
  d="canon_batches/$name"
  mkdir -p "$d"
  (cd "$d"; ../../enumerate_canon "$table" > stats.txt; awk '{gsub(/_/,"");print NR-1,$0}' open.txt | ../../farbank 5 > far5.txt 2>far.log)
  mod="Raw40C${name//_/}"
  python3 certify_canonical.py "$d" "$d/shards2" "$table" "$B" "$mod" 96
  (cd "$d/shards2"; export LEAN_PATH="$LEAN_PATH:$PWD"; lean -o "${mod}Base.olean" "${mod}Base.lean"; for f in "${mod}"Kid*.lean; do lean -o "${f%.lean}.olean" "$f"; done; lean -o "${mod}All.olean" "${mod}All.lean")
  export LEAN_PATH="$LEAN_PATH:$PWD/$d/shards2"
  names+=("$name")
done < canonical-accepted.txt
python3 gen_batch.py "${names[@]}" > Raw40BatchAccepted.lean
lean -o Raw40BatchAccepted.olean Raw40BatchAccepted.lean
