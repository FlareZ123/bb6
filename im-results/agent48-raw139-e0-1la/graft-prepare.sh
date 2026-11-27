#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
checker="$PWD/im-results/agent48-raw139-e0-0re"
graft="$PWD/im-results/agent3-raw139-oneLA8938"
block="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
work="$PWD/.tmp/a48-oneLA-graft"
export PYTHONPATH="$block:$old:$checker"
mkdir -p "$work/imports"
python3 "$graft/graft_oneLA.py" "$1/partition.json" "$1/spec-compact.json" "$base/extension.json.zlib.b64" "$work"
(cd "$work"; sha256sum -c <<'EOF'
e6debaf6d01e5b06bce2404a750899954fec2072f82b2b41634ac61c35ae540f  partition.json
0b1d01399e25c52e7413f6bd11e5e9dd7ce899c2e740f14efc9f8520ed54d0ef  spec-compact.json
EOF
)
python3 - "$work" <<'PY'
import json,pathlib,sys
w=pathlib.Path(sys.argv[1])
s=json.loads((w/'spec-compact.json').read_text())
assert s['bound']==881057
assert s['parent']==[7,24,11,24,14,24,24,16,2,11,24,24]
assert s['counts']['split']==40782
mapping={}
for p in s['proven'].values():
    if p.endswith(('Sweep4494','Sweep4700','Sweep9011','Sweep9012')):
        mod='OneLASweepBridge'
    elif p.endswith(('Sweep9138','Sweep9162')):
        mod='OneLAGrowth'
    elif p.endswith('Sweep8938'):
        mod='Sweep8938Bridge'
    elif p=='BB6.Agent48OneLALongCycle':
        mod='OneLALongCycle'
    elif p.startswith('BB6.Agent48Raw139E0OneLAExtensionBlocks.R'):
        mod='OneLAExtBlock'+p.rsplit('.R',1)[1]
    elif p.startswith('BB6.Agent48Wide'):
        mod=p.rsplit('.',1)[1]+'Proof'
    else:
        raise ValueError(p)
    mapping[p]=mod
assert set(mapping.values())==set(s['external_imports'])
s['external_module_by_namespace']=mapping
s['independent_root_children']=True
(w/'spec-package.json').write_text(json.dumps(s,separators=(',',':'))+'\n')
PY
python3 "$checker/package6.py" "$work/spec-package.json" "$work/partition.json" "$work/imports"
python3 "$base/plan-graft.py" "$work"
git rev-parse HEAD > "$work/source-sha"
