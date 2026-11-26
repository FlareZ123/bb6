#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1rb"
checker="$PWD/im-results/agent48-raw139-e0-0re"
block="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
work="$PWD/.tmp/a48-e0parent-OneRB"
export PYTHONPATH="$block:$old"
mkdir -p "$work/imports" "$work/build"
g++ -std=c++17 -O3 "$checker/replay.cpp" -o "$work/replay"
python3 "$checker/test_replay.py" "$work/replay"
"$work/replay" 450 2 7 24 11 24 14 24 24 16 7 11 24 24 > "$work/partition.json"
echo "2ab1b14dea5234bdd5c4dbc50280c4d86211d3d1a2f38ca4e06ecc74347445d0  $work/partition.json" | sha256sum -c -
python3 "$base/discover.py" "$work/partition.json" "$work/spec-compact.json"
python3 "$checker/package6.py" "$work/spec-compact.json" "$work/partition.json" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Raw139E0OneRBCover.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-oneRB-parent \
  --theorem BB6.Agent48Raw139E0OneRB.all_completions_weighted \
  --parent-table '[7,24,11,24,14,24,24,16,7,11,24,24]' --weighted-bound 103019 \
  --artifact-name raw139-e0parent-OneRB-certified \
  --provenance-input "$checker/replay.cpp" --provenance-input "$work/spec-compact.json" --provenance-input "$base/discover.py" \
  --provenance-input "$checker/package6.py" --provenance-input "$checker/test_replay.py" \
  --provenance-input "$block/blockcert.py" --provenance-input "$block/package.py" \
  --provenance-input "$old/scan.py" --provenance-input "$work/partition.json" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for theorem in ('hRoot','all_completions_weighted'):
    name='BB6.Agent48Raw139E0OneRB.'+theorem
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
