#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-oneLA-check"
out="$PWD/.tmp/a48-oneLA-final"
test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
mkdir -p "$out/build"
python3 im-results/agent13-coverage/unpack.py
python3 im-results/agent3-raw139-oneLA8938/unpack.py
shards=("$1"/raw139-oneLA-graft-shard-*)
test "${#shards[@]}" = 12
for d in "${shards[@]}"; do
  case "$(basename "$d")" in
    raw139-oneLA-graft-shard-10|raw139-oneLA-graft-shard-11)
      test "$(cat "$d/source-sha")" = 1a513302a4333d3aff095a9350281b35c3b9f209 ;;
    *) cmp "$work/source-sha" "$d/source-sha" ;;
  esac
done
python3 "$base/merge-graft.py" "$out/reuse" "$work" "${shards[@]}"
python3 tools/lean_compile_closure.py "$work/imports/Raw139E0OneLACover.lean" \
  --source-root "$work/imports" --source-root "$work/extern" \
  --workdir "$out/build" --jobs 2 --manifest "$out/manifest.json" \
  --precompiled-manifest "$out/reuse/manifest.json" --precompiled-dir "$out/reuse" \
  --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
  --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
  --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
  --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
  --label raw139-e0-oneLA-complete --theorem BB6.Agent48Raw139E0OneLA.all_completions_weighted \
  --parent-table '[7,24,11,24,14,24,24,16,2,11,24,24]' --weighted-bound 881057 \
  --artifact-name raw139-oneLA-graft-certified | tee "$out/log"
! grep -E 'sorryAx|native_decide|ofReduceBool|declaration uses .sorry.' "$out/log"
python3 - "$out/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
m=re.search(r"'BB6\.Agent48Raw139E0OneLA\.all_completions_weighted' depends on axioms: \[([^\]]*)\]",s)
assert m and set(x.strip() for x in m[1].split(',')) <= {'propext','Classical.choice','Quot.sound'}
PY
cp -r "$work/imports" "$work/extern" "$out/"
