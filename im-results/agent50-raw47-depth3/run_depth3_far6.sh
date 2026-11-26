#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
OUT="${1:-/tmp/raw47-depth3-far6}"
mkdir -p "$OUT"

OPEN="$ROOT/im-results/agent50-raw47-depth3/raw47-depth3.open"
FAR5="$ROOT/im-results/agent50-raw47-depth3/raw47-depth3-far5.txt"
test -s "$OPEN"
test -s "$FAR5"
awk '{print NR-1, $0}' "$OPEN" | tr -d '_' > "$OUT/raw47-depth3-farbank.in"
COUNT="$(wc -l < "$OUT/raw47-depth3-farbank.in" | tr -d ' ')"
test "$COUNT" -eq 1212
g++ -std=c++20 -O3 "$ROOT/im-results/agent19-raw40-cut/farbank.cpp" -o "$OUT/raw47-farbank"
/usr/bin/time -v "$OUT/raw47-farbank" 6 "$FAR5" < "$OUT/raw47-depth3-farbank.in" > "$OUT/raw47-depth3-far6.txt" 2> "$OUT/raw47-depth3-far6.log"

HITS="$(wc -l < "$OUT/raw47-depth3-far6.txt" | tr -d ' ')"
FAR5_HITS="$(wc -l < "$FAR5" | tr -d ' ')"
TOTAL=$((HITS + FAR5_HITS))
cat > "$OUT/summary.txt" <<EOF
Raw47 depth-3 FAR6 search
residuals=$COUNT
preloaded_far5_hits=$FAR5_HITS
new_far6_hits=$HITS
total_far5_or_far6_hits=$TOTAL
max_automaton_states=6
input_sha256=$(sha256sum "$OUT/raw47-depth3-farbank.in" | cut -d' ' -f1)
candidate_sha256=$(sha256sum "$OUT/raw47-depth3-far6.txt" | cut -d' ' -f1)
EOF
cat "$OUT/summary.txt"
cat "$OUT/raw47-depth3-far6.log"
cat "$OUT/raw47-depth3-far6.txt"
