#!/usr/bin/env bash
set -euo pipefail
base=im-results/agent14-raw139-e0-zeroLF
work=.tmp/a48-e0sweep-ZeroLF
mkdir -p "$work/imports" "$work/build"
python3 im-results/agent13-coverage/unpack.py
python3 "$base/replay.py"
python3 im-results/agent13-block-far/specialize.py 4
python3 "$base/emit9015.py" "$work/imports"
python3 tools/lean_compile_closure.py "$base/E0LFResidualAudit.lean" \
  --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-zeroLF-residual-audit \
  --theorem BB6Coverage.Agent14E0LFResidual2040.never \
  --artifact-name raw139-e0sweep-ZeroLF-certified \
  --provenance-input "$base/emit9015.py" \
  --provenance-input im-results/agent48-raw139-f1-oneRA/blockcert.py \
  --provenance-input im-results/agent48-raw139-f1-oneRA/package.py | tee "$work/log"
python3 - "$work/log" <<'PY'
import re,sys,pathlib
s=pathlib.Path(sys.argv[1]).read_text()
for name in [
  'BB6.Agent14E0LFResidualCycles.never3864',
  'BB6.Agent14E0LFResidualCycles.never4344',
  'BB6.Agent14E0LFResidualCycles.never11287',
  'BB6Coverage.Agent14E0LFResidual10338.never',
  'BB6Coverage.Agent14E0LFResidual2040.never',
  'BB6.Agent14E0LFResidual9015.never']:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
    used={a.strip() for a in m.group(1).split(',') if a.strip()} if m else set()
    assert m or "'"+name+"' does not depend on any axioms" in s, name
    assert used <= {'propext','Classical.choice','Quot.sound'},(name,used)
PY
