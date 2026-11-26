#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-0rd"
checker="$PWD/im-results/agent48-raw139-e0-0re"
block="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
work="$PWD/.tmp/a48-e0parent-ZeroRD"
export PYTHONPATH="$block:$old"
mkdir -p "$work/imports" "$work/build"
g++ -std=c++17 -O3 "$checker/replay.cpp" -o "$work/replay"
python3 "$checker/test_replay.py" "$work/replay"
"$work/replay" 450 2 7 24 11 24 14 24 24 16 13 11 24 24 > "$work/partition.json"
echo "4f8e9ab952fb342569e15d44cabcaa31c265cc9fe5f253d0258e91c32a99225c  $work/partition.json" | sha256sum -c -
python3 "$base/discover.py" "$work/partition.json" "$work/spec-compact.json"
python3 "$checker/package6.py" "$work/spec-compact.json" "$work/partition.json" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Raw139E0ZeroRDCover.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-zeroRD-parent \
  --theorem BB6.Agent48Raw139E0ZeroRD.all_completions_weighted \
  --parent-table '[7,24,11,24,14,24,24,16,13,11,24,24]' --weighted-bound 806 \
  --artifact-name raw139-e0parent-ZeroRD-certified \
  --provenance-input "$checker/replay.cpp" --provenance-input "$work/spec-compact.json" --provenance-input "$base/discover.py" \
  --provenance-input "$checker/package6.py" --provenance-input "$checker/test_replay.py" \
  --provenance-input "$block/blockcert.py" --provenance-input "$block/package.py" \
  --provenance-input "$old/scan.py" --provenance-input "$work/partition.json" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for theorem in ('hRoot','all_completions_weighted'):
    name='BB6.Agent48Raw139E0ZeroRD.'+theorem
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
