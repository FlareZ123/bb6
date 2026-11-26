#!/usr/bin/env bash
set -euo pipefail
base=im-results/agent48-raw139-e0-0re
work=.tmp/a48-e0sweep-ZeroRE
mkdir -p "$work/imports" "$work/build"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$base/E0ZeroRESweep.lean" \
  --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-zeroRE-sweep \
  --theorem BB6Coverage.Agent48E0ZeroRESweep.never \
  --parent-table '[7,21,11,24,14,23,3,16,17,11,15,20]' \
  --artifact-name raw139-e0sweep-ZeroRE-certified | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for theorem in ('growth','first','arbitraryRun','never'):
    name='BB6Coverage.Agent48E0ZeroRESweep.'+theorem
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
