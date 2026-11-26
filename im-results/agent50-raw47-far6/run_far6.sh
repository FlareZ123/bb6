#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
OUT="${1:-/tmp/raw47-far6}"
mkdir -p "$OUT"

g++ -std=c++20 -O3 "$ROOT/im-results/agent7-raw49/cut.cpp" -o "$OUT/raw47-cut"
"$OUT/raw47-cut" '1RB---_1RC---_0RD---_1LD0RC_------_------' 1000 32 2 "$OUT/raw47" | tee "$OUT/raw47-cut.log"
grep -q 'open=114 cycle=131 last=0 split=12 alias=32 max_query=10 max_cycle_end=267' "$OUT/raw47-cut.log"
cmp "$OUT/raw47.json" "$ROOT/im-results/agent19-d1-pilot/Raw47-cut.json"
cmp "$OUT/raw47.open" "$ROOT/im-results/agent19-d1-pilot/Raw47-open.txt"

awk '{print NR-1, $0}' "$OUT/raw47.open" | tr -d '_' > "$OUT/raw47-farbank.in"
g++ -std=c++20 -O3 "$ROOT/im-results/agent19-raw40-cut/farbank.cpp" -o "$OUT/raw47-farbank"
/usr/bin/time -v "$OUT/raw47-farbank" 6 < "$OUT/raw47-farbank.in" > "$OUT/raw47-far6.txt" 2> "$OUT/raw47-far6.log"

HITS="$(wc -l < "$OUT/raw47-far6.txt" | tr -d ' ')"
cat > "$OUT/summary.txt" <<EOF
Raw47 FAR6 search
parent=1RB---_1RC---_0RD---_1LD0RC_------_------
residuals=114
far5_hits=0
max_automaton_states=6
far6_hits=$HITS
input_sha256=$(sha256sum "$OUT/raw47-farbank.in" | cut -d' ' -f1)
candidate_sha256=$(sha256sum "$OUT/raw47-far6.txt" | cut -d' ' -f1)
EOF
cat "$OUT/summary.txt"
cat "$OUT/raw47-far6.log"
cat "$OUT/raw47-far6.txt"
