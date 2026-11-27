#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent3-raw139-e0-oneLB"
work="$PWD/.tmp/a48-e0sweep-OneLBReturn"
mkdir -p "$work/imports" "$work/build"
cp "$base"/Return{Core,RLE}.lean "$work/imports/"
python3 "$base/emit-return.py" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/OneLBReturnFinal.lean" \
 --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
 --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
 --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
 --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
 --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
 --manifest "$work/manifest.json" --label raw139-OneLB-A1-compressed \
 --theorem BB6.Agent3OneLBReturn.both_weighted \
 --artifact-name raw139-e0sweep-OneLBReturn-certified \
 --provenance-input "$base/emit-return.py" | tee "$work/log"
python3 - "$work/log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for t in ('readFinal0','readFinal1','both_weighted'):
 name='BB6.Agent3OneLBReturn.'+t
 m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
 if m:used={x.strip() for x in m.group(1).split(',') if x.strip()}
 elif "'"+name+"' does not depend on any axioms" in s:used=set()
 else:raise SystemExit('Missing axiom audit: '+name)
 assert used<={'propext','Classical.choice','Quot.sound'},(name,used)
 print(name,sorted(used))
PY
