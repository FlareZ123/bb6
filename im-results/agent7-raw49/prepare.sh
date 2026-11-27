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
# New completed cylinders, including asymmetric run-length stack invariants.
cp "$D/rest_sweep_recipes.jsonl" "$D/rle_recipes.jsonl" "$W/"
mkdir -p "$W/child15" "$W/child29"
python "$D/emit_sweep_recipes.py" "$W/rest_sweep_recipes.jsonl" BB6.Agent7Raw49RestSweeps "$W/child29/Raw49RestSweeps.lean"
PYTHONPATH="$D/../agent4-two-sided-automata" python "$D/emit_rle.py" "$W/rle_recipes.jsonl" BB6.Agent7Raw49RLE "$W/child15/Raw49RLE.lean"
cat "$D/bulk_far_seeds.txt" "$D/rest_far_seeds.txt" | sort -u > "$W/all_far_seeds.txt"
for i in 15 29 44 48 52 54 55 57 60 61 62 64 65 67 68 69 70 73 74 75 76 77 78 82 83 84 85 86 88 89 93 94 100 105 111 114 115 119 123; do
    p=$(sed -n "$((i+1))p" "$W/r49.open")
    "$W/cut" "$p" 1000 32 6 "$W/trials/$i"
    awk '{gsub(/_/,""); print NR-1,$0}' "$W/trials/$i.open" | "$W/farbank" 0 "$W/all_far_seeds.txt" > "$W/trials/$i.far" 2> "$W/trials/$i.far.log"
    python "$W/gen_child.py" "$i"
done
