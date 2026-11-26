#!/usr/bin/env bash
set -euo pipefail
base=im-results/agent48-raw139-e0-1la
work=.tmp/a48-e0sweep-OneLAGrowth
mkdir -p "$work/imports" "$work/build"
python3 - "$base" "$work" <<'PY'
import pathlib,hashlib,base64,zlib,sys
b,w=map(pathlib.Path,sys.argv[1:])
s=zlib.decompress(base64.b64decode((b/'OneLAGrowth.lean.zlib.b64').read_text()))
assert hashlib.sha256(s).hexdigest()=='8fe466b598a3d12e22d8dc11c2d76f6dafabe1eb8b32f9d84aa41d698d3bf088'
(w/'imports/OneLAGrowth.lean').write_bytes(s)
PY
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/OneLAGrowth.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-oneLA-two-growth \
  --theorem BB6.Agent48Raw139E0OneLASweeps.Sweep9138.never \
  --parent-table '[7,20,11,6,14,5,24,16,2,11,14,19]' \
  --artifact-name raw139-e0sweep-OneLAGrowth-certified | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for name in ('BB6Coverage.Agent48.OneLAGrowth.growth','BB6Coverage.Agent48.OneLAGrowth.entry','BB6Coverage.Agent48.OneLAGrowth.nonhalt','BB6.Agent48Raw139E0OneLASweeps.Sweep9138.never','BB6.Agent48Raw139E0OneLASweeps.Sweep9162.never'):
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
