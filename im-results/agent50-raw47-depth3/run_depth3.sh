#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
OUT="${1:-/tmp/raw47-depth3}"
mkdir -p "$OUT"

g++ -std=c++20 -O3 "$ROOT/im-results/agent7-raw49/cut.cpp" -o "$OUT/raw47-cut"
"$OUT/raw47-cut" '1RB---_1RC---_0RD---_1LD0RC_------_------' 1000 32 3 "$OUT/raw47-depth3" | tee "$OUT/raw47-depth3-cut.log"
test -s "$OUT/raw47-depth3.json"
test -s "$OUT/raw47-depth3.open"
awk '{print NR-1, $0}' "$OUT/raw47-depth3.open" | tr -d '_' > "$OUT/raw47-depth3-farbank.in"
g++ -std=c++20 -O3 "$ROOT/im-results/agent19-raw40-cut/farbank.cpp" -o "$OUT/raw47-farbank"
/usr/bin/time -v "$OUT/raw47-farbank" 5 < "$OUT/raw47-depth3-farbank.in" > "$OUT/raw47-depth3-far5.txt" 2> "$OUT/raw47-depth3-far5.log"

python - "$OUT" <<'PY'
from collections import Counter
from pathlib import Path
import hashlib, sys
out=Path(sys.argv[1])
rows=[x for x in (out/'raw47-depth3.open').read_text().splitlines() if x.strip()]
holes=Counter()
for row in rows:
    chunks=row.split('_')
    slots=[chunks[i][j:j+3] for i in range(6) for j in (0,3)]
    holes[sum(x=='---' for x in slots)] += 1
hits=sum(1 for x in (out/'raw47-depth3-far5.txt').read_text().splitlines() if x.strip())
summary=[
    'Raw47 depth-3 cut + FAR5 search',
    'parent=1RB---_1RC---_0RD---_1LD0RC_------_------',
    'cap=1000', 'lookback=32', 'split_depth=3',
    f'open={len(rows)}', f'unique_open={len(set(rows))}', f'duplicate_open={len(rows)-len(set(rows))}',
    'hole_distribution='+','.join(f'{k}:{holes[k]}' for k in sorted(holes)),
    f'far5_hits={hits}',
    f'open_sha256={hashlib.sha256((out/"raw47-depth3.open").read_bytes()).hexdigest()}',
    f'far5_sha256={hashlib.sha256((out/"raw47-depth3-far5.txt").read_bytes()).hexdigest()}',
]
(out/'summary.txt').write_text('\n'.join(summary)+'\n')
print('\n'.join(summary))
PY
cat "$OUT/raw47-depth3-cut.log"
cat "$OUT/raw47-depth3-far5.log"
cat "$OUT/raw47-depth3-far5.txt"
