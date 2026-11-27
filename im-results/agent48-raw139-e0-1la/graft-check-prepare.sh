#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-oneLA-check"
mkdir -p "$work/imports" "$work/extern" "$work/build"
original="$1"; graft="$2"; ext="$3"; wide="$4"; long="$5"; affine="$6"
test "$(cat "$graft/source-sha")" = 97d34779a50855ff40b480fff458aed96056d8f3
test "$(cat "$affine/source-sha")" = b8bc83e0fe56ca8e69557acfdddc9fe1a327195d
(cd "$graft"; sha256sum -c <<'EOF'
e6debaf6d01e5b06bce2404a750899954fec2072f82b2b41634ac61c35ae540f  partition.json
0b1d01399e25c52e7413f6bd11e5e9dd7ce899c2e740f14efc9f8520ed54d0ef  spec-compact.json
EOF
)
python3 im-results/agent13-coverage/unpack.py
python3 im-results/agent3-raw139-oneLA8938/unpack.py
overrides=(--override RootShift=im-results/agent8-coverage-contract/RootShift.lean
 --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean
 --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean
 --override Frontier=im-results/agent8-coverage-contract/Frontier.lean)
python3 tools/lean_compile_closure.py "$affine/Raw139Affine8938Never.lean" \
  --source-root "$affine" --artifact-dir "$affine/build" --manifest-only \
  --manifest "$affine/manifest.json" --compare-manifest "$affine/core-manifest.json" \
  --theorem BB6Coverage.Agent3Affine8938.never --label raw139-affine8938-accepted-reuse \
  "${overrides[@]}"
python3 - "$affine" "$ext" "$wide" "$long" "$work/extern" <<'PY'
import json,pathlib,shutil,sys
a,e,w,l,o=map(pathlib.Path,sys.argv[1:])
for p,run in [(e,45916031509),(w,45916452751),(l,45924267332)]:
    m=json.loads((p/'manifest.json').read_text());assert int(m['workflow']['run_id'])==run
    for s in (p/'imports').glob('*.lean'):
        d=o/s.name
        if d.exists():assert d.read_bytes()==s.read_bytes(),s
        else:shutil.copy2(s,d)
m=json.loads((a/'manifest.json').read_text())
c=json.loads((a/'core-manifest.json').read_text())
assert int(c['workflow']['run_id'])==45924271354
m['source_revisions']=[(a/'source-sha').read_text().strip()]
m['workflow']=c['workflow']
(a/'manifest.json').write_text(json.dumps(m))
for s in list(a.glob('*.lean'))+list((a/'generated').glob('*.lean')):
    d=o/s.name
    if d.exists():assert d.read_bytes()==s.read_bytes(),s
    else:shutil.copy2(s,d)
PY
python3 "$base/merge-graft.py" "$work/reuse" "$ext" "$wide" "$long" "$affine"
python3 "$base/transform-graft.py" "$graft/imports" "$work/imports" "$original/partition.json" "$original/spec-compact.json" 10000
python3 "$base/emit_late.py" "$original/partition.json" "$original/spec-compact.json" "$work/extern" 10000
cp "$graft/shard-plan.json" "$work/"
cp "$graft/source-sha" "$work/graft-source-sha"
roots=()
while read -r m; do roots+=("$work/extern/$m.lean"); done < "$work/extern/late-roots.txt"
roots+=("$base/WeightedAudit.lean" "$base/OneLALate3318Sharp.lean" "$base/OneLASweepBridge.lean"
 "$PWD/im-results/agent3-raw139-oneLA8938/Sweep8938Bridge.lean"
 "$work/extern/OneLALongCycle.lean" "$work/extern/OneLAExtension.lean" "$work/extern/OneLAWide.lean")
python3 tools/lean_compile_closure.py "${roots[@]}" \
  --source-root "$work/extern" --workdir "$work/build" --jobs 2 \
  --precompiled-manifest "$work/reuse/manifest.json" --precompiled-dir "$work/reuse" \
  --manifest "$work/manifest.json" --label raw139-oneLA-common-dependencies \
  "${overrides[@]}" | tee "$work/log"
! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$work/log"
git rev-parse HEAD > "$work/source-sha"
