#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent3-raw139-e0-oneLB"
checker="$PWD/im-results/agent48-raw139-e0-0re"
block="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
work="$PWD/.tmp/a48-e0parent-OneLBC1OneLC"
export PYTHONPATH="$block:$old:$checker"
mkdir -p "$work/raw-imports" "$work/imports" "$work/build"
late="$PWD/im-results/agent48-raw139-e0-1la"
g++ -std=c++17 -O3 "$checker/replay.cpp" -o "$work/replay"
python3 "$checker/test_replay.py" "$work/replay"
"$work/replay" 450 2 7 24 11 24 14 10 24 16 6 11 24 24 > "$work/partition.json"
python3 "$base/discover-oneLC.py" "$work/partition.json" "$work/spec-compact.json" | tee "$work/discovery.log"
python3 "$checker/package6.py" "$work/spec-compact.json" "$work/partition.json" "$work/raw-imports"
python3 "$late/emit_late.py" "$work/partition.json" "$work/spec-compact.json" "$work/imports" 10000
python3 "$late/transform-graft.py" "$work/raw-imports" "$work/imports" "$work/partition.json" "$work/spec-compact.json" 10000
# The shared emitter originally names its leaf modules OneLALate*. Make
# these distinct before compilation, including namespaces and imports.
python3 - "$work/imports" <<'PY'
import pathlib,sys
d=pathlib.Path(sys.argv[1])
for p in list(d.glob("*.lean")):
    s=p.read_text().replace("OneLALate","OneLBC1OneLCLate")
    q=p.with_name(p.name.replace("OneLALate","OneLBC1OneLCLate"))
    if q!=p:p.unlink()
    q.write_text(s)
PY
cat > "$work/imports/Raw139E0OneLBC1OneLCWeighted.lean" <<'LEAN'
import Raw139E0OneLBC1OneLCCover
namespace BB6.Agent3E0OneLBC1OneLC
open BB6Coverage BB6.Agent13BlankDelay
theorem weighted : Cover (WeightedBound 61185) parent :=
  Cover.leaf _ all_completions_weighted
#print axioms weighted
end BB6.Agent3E0OneLBC1OneLC
LEAN
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Raw139E0OneLBC1OneLCWeighted.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
  --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
  --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
  --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
  --manifest "$work/manifest.json" --label raw139-e0-oneLB-c1-zeroLC \
  --theorem BB6.Agent3E0OneLBC1OneLC.weighted \
  --parent-table '[7,24,11,24,14,10,24,16,6,11,24,24]' --weighted-bound 61185 \
  --artifact-name raw139-e0parent-OneLBC1OneLC-certified \
  --provenance-input "$checker/replay.cpp" --provenance-input "$work/partition.json" \
  --provenance-input "$work/spec-compact.json" --provenance-input "$base/discover-oneLC.py" \
  --provenance-input "$checker/package6.py" \
  --provenance-input "$block/blockcert.py" --provenance-input "$block/package.py" \
  --provenance-input "$old/scan.py" --provenance-input "$late/emit_late.py" \
  --provenance-input "$late/transform-graft.py" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for theorem in ('hRoot','all_completions_weighted','weighted'):
    name='BB6.Agent3E0OneLBC1OneLC.'+theorem
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
