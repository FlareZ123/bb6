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
