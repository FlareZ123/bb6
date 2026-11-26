#!/usr/bin/env bash
set -euo pipefail
base=im-results/agent14-raw139-e0-zeroLF
context=im-results/agent3-raw139-zeroLF-context
block=im-results/agent13-block-far
work=.tmp/a6-zeroLF
python3 im-results/agent13-coverage/unpack.py
python3 "$block/specialize.py" 4 12
python3 - "$block" <<'PY'
from pathlib import Path
import re,sys
root=Path(sys.argv[1])
s=(root/'SparseBlockFAR.lean').read_text().replace('import BlockFAR','import BlockFAR12').replace('BB6BlockFAR','BB6BlockFAR12')
s=re.sub(r'\b48\b',str(6*4096),s)
s=re.sub(r'\b8\b','4096',s)
(root/'SparseBlockFAR12.lean').write_text(s)
sys.path.insert(0,str(root))
from emit_active import specialize_active
specialize_active(root,12)
PY
if [[ "${1:-}" == sources ]]; then
  mkdir -p "$work/imports"
  g++ -O3 -std=c++17 "$base/replay.cpp" -o "$work/replay"
  "$work/replay" > "$work/partition.json"
  python3 "$base/assemble.py" "$work/imports" --partition "$work/partition.json" --packed
  python3 "$base/assemble.py" "$work/imports" --final
  python3 "$base/emit9015.py" "$work/imports"
  python3 "$context/emit4125.py" "$work/imports"
  python3 "$context/emit3002.py" "$work/imports"
  python3 "$context/emit1307.py" "$work/imports"
  tmp=$(mktemp -d)
  python3 "$base/emit_cycle3863_packed.py" "$tmp/E0LF3863Packed.lean"
  python3 "$base/shard3863.py" "$tmp/E0LF3863Packed.lean" "$work/imports"
  rm -rf "$tmp"
fi
