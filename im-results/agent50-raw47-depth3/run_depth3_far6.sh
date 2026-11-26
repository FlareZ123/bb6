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
awk '{print $2}' "$FAR5" > "$OUT/raw47-depth3-far5.codes"
FAR5_HITS="$(wc -l < "$OUT/raw47-depth3-far5.codes" | tr -d ' ')"
test "$FAR5_HITS" -eq 10
python - "$OUT/raw47-depth3-far5.codes" <<'PY'
from pathlib import Path
import sys
codes=Path(sys.argv[1]).read_text().split()
assert len(codes)==10, len(codes)
for code in codes:
    n=(len(code)-1)//2
    assert 1 <= n <= 5 and len(code)==2*n+1 and code[0] in "01", code
    assert all(c.isdigit() and int(c)<n for c in code[1:]), code
PY
g++ -std=c++20 -O3 "$ROOT/im-results/agent19-raw40-cut/farbank.cpp" -o "$OUT/raw47-farbank"
/usr/bin/time -v "$OUT/raw47-farbank" 6 "$OUT/raw47-depth3-far5.codes" < "$OUT/raw47-depth3-farbank.in" > "$OUT/raw47-depth3-far6.txt" 2> "$OUT/raw47-depth3-far6.log"

HITS="$(wc -l < "$OUT/raw47-depth3-far6.txt" | tr -d ' ')"
NEW=$((HITS - FAR5_HITS))
test "$NEW" -ge 0
cat > "$OUT/summary.txt" <<EOF
Raw47 depth-3 FAR6 search
residuals=$COUNT
preloaded_far5_codes=$FAR5_HITS
preloaded_far5_matches=$FAR5_HITS
new_far6_matches=$NEW
total_far5_or_far6_matches=$HITS
max_automaton_states=6
input_sha256=$(sha256sum "$OUT/raw47-depth3-farbank.in" | cut -d' ' -f1)
preload_codes_sha256=$(sha256sum "$OUT/raw47-depth3-far5.codes" | cut -d' ' -f1)
candidate_sha256=$(sha256sum "$OUT/raw47-depth3-far6.txt" | cut -d' ' -f1)
EOF
cat "$OUT/summary.txt"
cat "$OUT/raw47-depth3-far6.log"
cat "$OUT/raw47-depth3-far6.txt"
