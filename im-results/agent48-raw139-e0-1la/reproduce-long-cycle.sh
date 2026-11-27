#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-e0sweep-OneLALongCycle"
mkdir -p "$work/imports" "$work/build"
python3 "$base/emit-long-cycle.py" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/OneLALongCycle.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-oneLA-long-cycle \
  --theorem BB6.Agent48OneLALongCycle.never \
  --parent-table '[7,20,11,7,14,1,24,16,2,11,8,4]' \
  --artifact-name raw139-e0sweep-OneLALongCycle-certified | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for n in ('checked','never'):
    match=re.search(r"'BB6\.Agent48OneLALongCycle\."+n+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
    assert match and set(x.strip() for x in match.group(1).split(',')) <= {'propext','Classical.choice','Quot.sound'}, n
PY
