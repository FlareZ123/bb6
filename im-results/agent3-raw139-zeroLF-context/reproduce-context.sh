#!/usr/bin/env bash
set -euo pipefail
base=im-results/agent3-raw139-zeroLF-context
block=im-results/agent13-block-far
width="$1"
case "$width" in
  2) sibling=ZeroLFContext ;;
  12) sibling=ZeroLF1307 ;;
  *) exit 2 ;;
esac
work=".tmp/a48-e0sweep-$sibling"
mkdir -p "$work/imports" "$work/build"
python3 im-results/agent13-coverage/unpack.py
if [[ "$width" == 2 ]]; then
  python3 "$block/specialize.py" 4
  python3 "$base/emit4125.py" "$work/imports"
  python3 "$base/emit3002.py" "$work/imports"
  roots=("$work/imports/E0LFResidual4125.lean" "$work/imports/E0LFResidual3002.lean" "$base/E0LFSweep.lean")
  names=(BB6.Agent3E0LFResidual4125.never BB6.Agent3E0LFResidual3002.never BB6Coverage.Agent3E0LFSweep.stable_never)
else
  python3 "$block/specialize.py" 12
  python3 - "$block" <<'PY'
from pathlib import Path
import re,sys
root=Path(sys.argv[1])
s=(root/'SparseBlockFAR.lean').read_text().replace('import BlockFAR','import BlockFAR12').replace('BB6BlockFAR','BB6BlockFAR12')
s=re.sub(r'\b48\b',str(6*4096),s)
s=re.sub(r'\b8\b','4096',s)
(root/'SparseBlockFAR12.lean').write_text(s)
sys.path.insert(0,str(root))
from emit_active import specialize_active
specialize_active(root,12)
PY
  python3 "$base/emit1307.py" "$work/imports"
  roots=("$work/imports/E0LFResidual1307.lean")
  names=(BB6.Agent3E0LFResidual1307.never)
fi
python3 tools/lean_compile_closure.py "${roots[@]}" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 2 \
  --manifest "$work/manifest.json" --label "raw139-e0-zeroLF-$sibling" \
  --theorem "${names[0]}" --artifact-name "raw139-e0sweep-$sibling-certified" \
  --provenance-input "$base/emit4125.py" \
  --provenance-input "$base/emit3002.py" \
  --provenance-input "$base/emit1307.py" \
  --provenance-input "$base/sparse_min.py" \
  --provenance-input im-results/agent48-raw139-f1-oneRA/blockcert.py \
  --provenance-input im-results/agent48-raw139-f1-oneRA/package.py \
  --provenance-input "$block/emit_active.py" | tee "$work/log"
python3 - "$work/log" "${names[@]}" <<'PY'
import re,sys,pathlib
s=pathlib.Path(sys.argv[1]).read_text()
for name in sys.argv[2:]:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
    used={a.strip() for a in m.group(1).split(',') if a.strip()} if m else set()
    assert m or "'"+name+"' does not depend on any axioms" in s,name
    assert used <= {'propext','Classical.choice','Quot.sound'},(name,used)
    print(name,sorted(used))
PY
