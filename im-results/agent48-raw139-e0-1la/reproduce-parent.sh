#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
checker="$PWD/im-results/agent48-raw139-e0-0re"
block="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
work="$PWD/.tmp/a48-e0parent-OneLA"
export PYTHONPATH="$block:$old:$checker"
mkdir -p "$work/imports" "$work/build"
g++ -std=c++17 -O3 "$checker/replay.cpp" -o "$work/replay"
python3 "$checker/test_replay.py" "$work/replay"
"$work/replay" 450 2 7 24 11 24 14 24 24 16 2 11 24 24 > "$work/partition.json"
python3 "$base/discover.py" "$work/partition.json" "$work/spec-compact.json" "$work/unresolved.json" | tee "$work/discovery.log"
bound=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["bound"])' "$work/spec-compact.json")
cp "$base"/Sweep4494.lean "$base"/Sweep9011.lean "$base"/OneLASweepBridge.lean "$work/imports/"
python3 "$checker/package6.py" "$work/spec-compact.json" "$work/partition.json" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Raw139E0OneLACover.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-oneLA-parent \
  --theorem BB6.Agent48Raw139E0OneLA.all_completions_weighted \
  --parent-table '[7,24,11,24,14,24,24,16,2,11,24,24]' --weighted-bound "$bound" \
  --artifact-name raw139-e0parent-OneLA-certified \
  --provenance-input "$checker/replay.cpp" --provenance-input "$work/spec-compact.json" --provenance-input "$base/discover.py" \
  --provenance-input "$checker/package6.py" --provenance-input "$checker/test_replay.py" \
  --provenance-input "$block/blockcert.py" --provenance-input "$block/package.py" \
  --provenance-input "$old/scan.py" --provenance-input "$work/partition.json" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for theorem in ('hRoot','all_completions_weighted'):
    name='BB6.Agent48Raw139E0OneLA.'+theorem
    match=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
    if match:
        used={x.strip() for x in match.group(1).split(',') if x.strip()}
    elif "'"+name+"' does not depend on any axioms" in s:
        used=set()
    else:
        raise SystemExit('Missing axiom audit: '+name)
    assert used <= {'propext','Classical.choice','Quot.sound'}, (name,used)
    print(name,sorted(used))
PY
