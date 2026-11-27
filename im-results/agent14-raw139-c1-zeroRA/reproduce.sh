#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"
base="$(realpath "$1")"
work="$(realpath -m "$2")"
here=im-results/agent14-raw139-c1-zeroRA
saved=im-results/agent41-raw139-c1-zeroRA
mkdir -p "$work/imports" "$work/build"
python3 im-results/agent13-coverage/unpack.py
python3 "$saved/reproduce_trace.py" "$work/imports" 2 --sources-only
python3 "$here/generate.py" "$work/imports"
# Pin the common source paths used by the accepted C1 batch. The closure
# helper verifies source and import identities before reusing its objects.
mapfile -t overrides < <(python3 - "$base/manifest.json" <<'PY'
import json,sys
from pathlib import Path
for m in json.load(open(sys.argv[1]))['modules']:
    p=Path(m['source_path'])
    if p.is_file() and not m['module'].startswith('Raw139C1'):
        print('--override')
        print(m['module']+'='+str(p))
PY
)
python3 tools/lean_compile_closure.py \
  "$work/imports/A14C1RAParent.lean" \
  --source-root "$work/imports" --jobs 4 --workdir "$work/build" \
  --precompiled-manifest "$base/manifest.json" --precompiled-dir "$base/build" \
  --manifest "$work/manifest.json" \
  --label raw139-c1-zeroRA \
  --theorem BB6.Agent14Raw139C1ZeroRA.weighted \
  --parent-table '[7,24,11,24,14,1,3,16,12,11,24,24]' \
  --weighted-bound 14876970 --artifact-name raw139-c1-zeroRA-certified \
  --override Hybrid=im-results/agent6-raw139-e0-zeroRC/Hybrid.lean \
  --provenance-input "$here/generate.py" \
  --provenance-input "$saved/spec.json" \
  --provenance-input "$saved/SegmentTrace.lean.xz.b64" \
  --provenance-input "$saved/reproduce_trace.py" \
  --provenance-input im-results/agent48-raw139-f1-oneLA/scan.py \
  --provenance-input im-results/agent48-raw139-f1-oneRA/blockcert.py \
  --provenance-input im-results/agent48-raw139-f1-oneRA/package.py \
  "${overrides[@]}" | tee "$work/log"
! grep -Eq 'sorryAx|Lean\.ofReduceBool' "$work/log"
grep -F "'BB6.Agent14Raw139C1ZeroRA.weighted' depends on axioms: [propext, Classical.choice, Quot.sound]" "$work/log"
