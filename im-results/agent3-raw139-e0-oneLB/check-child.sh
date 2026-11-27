#!/usr/bin/env bash
set -euo pipefail
c="$1"; src="$2"; base="$PWD/im-results/agent3-raw139-e0-oneLB"
checker="$PWD/im-results/agent48-raw139-e0-0re"
block="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
late="$PWD/im-results/agent48-raw139-e0-1la"
export PYTHONPATH="$block:$old:$checker"
work="$PWD/.tmp/a3-oneLB-c$c"
mkdir -p "$work/imports" "$work/build"
python3 "$base/graft.py" "$src/c$c" "$work" "$c"
if [[ "$c" == "01" ]]; then
  cp im-results/agent12-raw139-oneLB-c1-286/Counter286{,Bridge}.lean "$work/imports/"
fi
if [[ "$(cat "$work/wide.json")" != "{}" ]]; then
  python3 "$base/emit-wide.py" "$work/imports" "$work/wide.json"
fi
python3 "$checker/package6.py" "$work/spec-compact.json" "$work/partition.json" "$work/raw-imports"
python3 "$late/emit_late.py" "$work/partition.json" "$work/spec-compact.json" "$work/imports" 10000
python3 "$late/transform-graft.py" "$work/raw-imports" "$work/imports" "$work/partition.json" "$work/spec-compact.json" 10000
rm -rf "$work/raw-imports"
python3 - "$work" "$c" <<'PY'
import pathlib,sys,json
w=pathlib.Path(sys.argv[1]);c=sys.argv[2];d=w/'imports';s=json.loads((w/'spec-compact.json').read_text())
for p in list(d.glob('*.lean')):
 txt=p.read_text().replace('OneLALate','OneLBC'+c+'Late')
 q=p.with_name(p.name.replace('OneLALate','OneLBC'+c+'Late'))
 if q!=p:p.unlink()
 q.write_text(txt)
ns=s['namespace'];B=s['bound'];prefix=s['prefix']
(d/(prefix+'Weighted.lean')).write_text(f"""import {prefix}Cover
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay
theorem weighted : Cover (WeightedBound {B}) parent := Cover.leaf _ all_completions_weighted
#print axioms weighted
end {ns}
""")
PY
readarray -t meta < <(python3 - "$work/spec-compact.json" <<'PY'
import sys,json
s=json.load(open(sys.argv[1]));print(s['prefix']);print(s['namespace']);print(s['bound']);print(json.dumps(s['parent']))
PY
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/${meta[0]}Weighted.lean" \
 --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
 --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
 --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
 --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
 --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
 --manifest "$work/manifest.json" --label "raw139-e0-OneLB-c$c" \
 --theorem "${meta[1]}.weighted" --parent-table "${meta[3]}" --weighted-bound "${meta[2]}" \
 --artifact-name "raw139-oneLB-c$c-certified" --provenance-input "$work/partition.json" \
 --provenance-input "$work/spec-compact.json" --provenance-input "$base/residuals.json" \
 --provenance-input "$base/graft.py" --provenance-input "$base/emit-wide.py" \
 --provenance-input "$checker/package6.py" --provenance-input "$late/transform-graft.py" \
 --provenance-input "$late/emit_late.py" | tee "$work/log"
python3 - "$work/log" "${meta[1]}" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for theorem in ('hRoot','all_completions_weighted','weighted'):
 name=sys.argv[2]+'.'+theorem
 m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
 if m:used={x.strip() for x in m.group(1).split(',') if x.strip()}
 elif "'"+name+"' does not depend on any axioms" in s:used=set()
 else:raise SystemExit('Missing axiom audit: '+name)
 assert used<={'propext','Classical.choice','Quot.sound'},(name,used)
 print(name,sorted(used))
PY
