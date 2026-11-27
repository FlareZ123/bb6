#!/usr/bin/env bash
set -euo pipefail
work="$PWD/.tmp/a48-oneLA-check"
out="$PWD/.tmp/a48-oneLA-shard"
test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
mkdir -p "$out/build"
python3 im-results/agent13-coverage/unpack.py
python3 im-results/agent3-raw139-oneLA8938/unpack.py
mapfile -t roots < <(python3 - "$work" "$SHARD" <<'PY'
import sys,json,pathlib
p=pathlib.Path(sys.argv[1]);groups=json.loads((p/'shard-plan.json').read_text())
assert len(groups)==12
for m in groups[int(sys.argv[2])]:print(p/'imports'/f'{m}.lean')
PY
)
test "${#roots[@]}" -gt 0
python3 tools/lean_compile_closure.py "${roots[@]}" \
  --source-root "$work/imports" --source-root "$work/extern" \
  --workdir "$out/build" --jobs 2 --manifest "$out/manifest.json" \
  --precompiled-manifest "$work/manifest.json" --precompiled-dir "$work/build" \
  --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
  --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
  --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
  --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
  --label "raw139-oneLA-shard-$SHARD" | tee "$out/log"
! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$out/log"
cp "$work/source-sha" "$out/"
