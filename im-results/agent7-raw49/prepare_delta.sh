#!/usr/bin/env bash
set -euo pipefail
D="$(cd "$(dirname "$0")" && pwd)"
W="$1"; shift
test "$#" -gt 0
mkdir -p "$W/trials"
cp "$D/gen_child.py" "$D/sweep_recipes.jsonl" "$D/rest_sweep_recipes.jsonl" "$D/rle_recipes.jsonl" "$W/"
g++ -std=c++20 -O3 "$D/cut.cpp" -o "$W/cut"
g++ -std=c++20 -O3 "$D/../agent19-raw40-cut/farbank.cpp" -o "$W/farbank"
"$W/cut" 1RB---_1RC---_0RD---_1LD1RC_------_------ 1000 32 2 "$W/r49"
test "$(wc -l < "$W/r49.open")" -eq 125
cat "$D/bulk_far_seeds.txt" "$D/rest_far_seeds.txt" | sort -u > "$W/all_far_seeds.txt"
for i in "$@"; do
    p=$(sed -n "$((i+1))p" "$W/r49.open")
    "$W/cut" "$p" 1000 32 6 "$W/trials/$i"
    awk '{gsub(/_/,""); print NR-1,$0}' "$W/trials/$i.open" | "$W/farbank" 0 "$W/all_far_seeds.txt" > "$W/trials/$i.far" 2> "$W/trials/$i.far.log"
    python "$W/gen_child.py" "$i"
done
