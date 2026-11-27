#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-oneRA"
old="$PWD/im-results/agent48-raw139-e0-1la"
checker="$PWD/im-results/agent48-raw139-e0-0re"
block="$PWD/im-results/agent48-raw139-f1-oneRA"
scan="$PWD/im-results/agent48-raw139-f1-oneLA"
work="$PWD/.tmp/a48-oneRA"
stage="${1:?prepare, shard, or join}"
export PYTHONPATH="$block:$scan:$checker"
mkdir -p "$work"
overrides=(--override RootShift=im-results/agent8-coverage-contract/RootShift.lean
 --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean
 --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean
 --override Frontier=im-results/agent8-coverage-contract/Frontier.lean)
# The original repository semantic modules, not a substitute fixture.
python3 im-results/agent13-coverage/unpack.py
if [[ "$stage" == prepare ]]; then
  mkdir -p "$work/build" "$work/extern"
  g++ -std=c++17 -O3 "$checker/replay.cpp" -o "$work/replay"
  "$work/replay" 450 2 7 24 11 24 14 24 24 16 3 11 24 24 > "$work/raw-partition.json"
  python3 "$base/prepare.py" "$work/raw-partition.json" "$work"
  python3 "$base/generate-parent.py" "$work/partition.json" "$work/spec-compact.json" "$work"
  rm -r "$work/ordinary"
  python3 "$base/emit_late.py" "$work/partition.json" "$work/spec-compact.json" "$work/extern" 10000
  roots=("$base/H4620.lean" "$old/WeightedAudit.lean")
  for w in 2 3 4; do roots+=("$work/extern/OneRASparse$w.lean"); done
  while read -r m; do roots+=("$work/extern/$m.lean"); done < "$work/extern/late-roots.txt"
  python3 tools/lean_compile_closure.py "${roots[@]}" --source-root "$work/extern" \
    --workdir "$work/build" --jobs 3 --manifest "$work/manifest.json" \
    --label raw139-oneRA-common "${overrides[@]}" | tee "$work/log"
  ! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$work/log"
  git rev-parse HEAD > "$work/source-sha"
elif [[ "$stage" == shard ]]; then
  test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
  out="$PWD/.tmp/a48-oneRA-shard"; mkdir -p "$out/build"
  mapfile -t roots < <(python3 - "$work" "${SHARD:?}" <<'PY'
import sys,json,pathlib
p=pathlib.Path(sys.argv[1]);g=json.loads((p/'shard-plan.json').read_text())
assert len(g)==12
for m in g[int(sys.argv[2])]: print(p/'imports'/f'{m}.lean')
PY
)
  test "${#roots[@]}" -gt 0
  python3 tools/lean_compile_closure.py "${roots[@]}" --source-root "$work/imports" \
    --source-root "$work/extern" --workdir "$out/build" --jobs 2 \
    --precompiled-manifest "$work/manifest.json" --precompiled-dir "$work/build" \
    --manifest "$out/manifest.json" --label "raw139-oneRA-shard-$SHARD" \
    "${overrides[@]}" | tee "$out/log"
  ! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$out/log"
  cp "$work/source-sha" "$out/"
elif [[ "$stage" == join ]]; then
  test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
  out="$PWD/.tmp/a48-oneRA-final"; mkdir -p "$out/build"
  shards=("${2:?shard artifact directory}"/raw139-oneRA-shard-*)
  test "${#shards[@]}" = 12
  for d in "${shards[@]}"; do cmp "$work/source-sha" "$d/source-sha"; done
  python3 "$old/merge-graft.py" "$out/reuse" "$work" "${shards[@]}"
  python3 tools/lean_compile_closure.py "$work/imports/Raw139E0OneRACover.lean" \
    --source-root "$work/imports" --source-root "$work/extern" --workdir "$out/build" --jobs 2 \
    --precompiled-manifest "$out/reuse/manifest.json" --precompiled-dir "$out/reuse" \
    --manifest "$out/manifest.json" --label raw139-e0-oneRA-complete \
    --theorem BB6.Agent48Raw139E0OneRA.all_completions_weighted \
    --parent-table '[7,24,11,24,14,24,24,16,3,11,24,24]' --weighted-bound 529714 \
    --artifact-name raw139-oneRA-certified "${overrides[@]}" | tee "$out/log"
  ! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$out/log"
  python3 - "$out/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
m=re.search(r"'BB6\.Agent48Raw139E0OneRA\.all_completions_weighted' depends on axioms: \[([^\]]*)\]",s)
assert m and set(x.strip() for x in m[1].split(',')) <= {'propext','Classical.choice','Quot.sound'}
PY
  cp -r "$work/imports" "$work/extern" "$out/"
else
  echo "unknown stage: $stage" >&2; exit 2
fi
