#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
SHARD="${1:?shard index required}"
SHARDS="${2:-4}"
OUT="${3:-/tmp/raw47-far7-shard-$SHARD}"
if (( SHARD < 0 || SHARD >= SHARDS )); then echo "invalid shard $SHARD/$SHARDS" >&2; exit 2; fi
mkdir -p "$OUT"

g++ -std=c++20 -O3 "$ROOT/im-results/agent7-raw49/cut.cpp" -o "$OUT/raw47-cut"
"$OUT/raw47-cut" '1RB---_1RC---_0RD---_1LD0RC_------_------' 1000 32 2 "$OUT/raw47" | tee "$OUT/raw47-cut.log"
grep -q 'open=114 cycle=131 last=0 split=12 alias=32 max_query=10 max_cycle_end=267' "$OUT/raw47-cut.log"
cmp "$OUT/raw47.json" "$ROOT/im-results/agent19-d1-pilot/Raw47-cut.json"
cmp "$OUT/raw47.open" "$ROOT/im-results/agent19-d1-pilot/Raw47-open.txt"

awk -v shard="$SHARD" -v shards="$SHARDS" '((NR-1) % shards) == shard {print NR-1, $0}' "$OUT/raw47.open" | tr -d '_' > "$OUT/raw47-far7.in"
COUNT="$(wc -l < "$OUT/raw47-far7.in" | tr -d ' ')"
if (( COUNT < 28 || COUNT > 29 )); then echo "unexpected shard size: $COUNT" >&2; exit 1; fi

g++ -std=c++20 -O3 "$ROOT/im-results/agent19-raw40-cut/farbank.cpp" -o "$OUT/raw47-farbank"
/usr/bin/time -v "$OUT/raw47-farbank" 7 < "$OUT/raw47-far7.in" > "$OUT/raw47-far7.txt" 2> "$OUT/raw47-far7.log"

HITS="$(wc -l < "$OUT/raw47-far7.txt" | tr -d ' ')"
cat > "$OUT/raw47-far7-shard-summary.txt" <<EOF
shard=$SHARD/$SHARDS
residuals=$COUNT
max_automaton_states=7
far7_hits=$HITS
input_sha256=$(sha256sum "$OUT/raw47-far7.in" | cut -d' ' -f1)
candidate_sha256=$(sha256sum "$OUT/raw47-far7.txt" | cut -d' ' -f1)
EOF
cat "$OUT/raw47-far7-shard-summary.txt"
cat "$OUT/raw47-far7.log"
