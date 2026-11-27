#!/usr/bin/env bash
set -euo pipefail
work=/tmp/8938lean
test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
test "$(find /tmp/8938shard -name '*.olean' | wc -l)" = 127
cp /tmp/8938shard/*.olean "$work/build/"
export LEAN_PATH="$work/build"
for name in SeedReach GrowthReach Raw139Affine8938Never; do
  lean -j 1 --root="$work" -o "$work/build/$name.olean" "$work/$name.lean" 2>&1 | tee "$work/$name.log"
  ! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$work/$name.log"
done
python3 - "$work/Raw139Affine8938Never.log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for name in ('authentic_seed','never'):
    m=re.search(r"'BB6Coverage.Agent3Affine8938\."+name+r"' depends on axioms: \[([^\]]*)\]",s)
    assert m, name
    assert set(x.strip() for x in m[1].split(',')) <= {'propext','Classical.choice','Quot.sound'},m[1]
PY
