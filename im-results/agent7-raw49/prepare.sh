#!/usr/bin/env bash
set -euo pipefail
D="$(cd "$(dirname "$0")" && pwd)"
W="$1"
mkdir -p "$W/trials"
cp "$D/gen_child.py" "$W/"
g++ -std=c++20 -O3 "$D/cut.cpp" -o "$W/cut"
"$W/cut" 1RB---_1RC---_0RD---_1LD1RC_------_------ 1000 32 2 "$W/r49"
test "$(wc -l < "$W/r49.open")" -eq 125
for i in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14; do
    p=$(sed -n "$((i+1))p" "$W/r49.open")
    "$W/cut" "$p" 1000 32 6 "$W/trials/$i"
    cp "$D/far$i.txt" "$W/trials/$i.far"
    python "$W/gen_child.py" "$i"
done
# Replay finite seed certificates; no DFA enumeration is needed.
cp "$D/sweep_recipes.jsonl" "$W/"
mkdir -p "$W/child16"
python "$D/emit_sweep_recipes.py" "$W/sweep_recipes.jsonl" BB6.Agent7Raw49BulkRecipes "$W/child16/Raw49BulkRecipes.lean"
g++ -std=c++20 -O3 "$D/../agent19-raw40-cut/farbank.cpp" -o "$W/farbank"
for i in 16 17 18 19 20 21 22 24 25; do
    p=$(sed -n "$((i+1))p" "$W/r49.open")
    "$W/cut" "$p" 1000 32 6 "$W/trials/$i"
    awk '{gsub(/_/,""); print NR-1,$0}' "$W/trials/$i.open" | "$W/farbank" 0 "$D/bulk_far_seeds.txt" > "$W/trials/$i.far" 2> "$W/trials/$i.far.log"
    python "$W/gen_child.py" "$i"
done
