#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-e0long"
test "$(git rev-parse HEAD)" = "$(cat "$work/source-sha")"
python3 - "$work" "$1" <<'PY'
import hashlib,pathlib,shutil,sys
work,shards=map(pathlib.Path,sys.argv[1:])
expected=set((work/'imports/shard-modules.txt').read_text().splitlines())
seen=set()
dirs=sorted(shards.glob('raw139-oneLA-packed-shard-*'))
assert len(dirs)==8,dirs
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for d in dirs:
    assert (d/'source-sha').read_bytes()==(work/'source-sha').read_bytes()
    for line in (d/'objects.sha256').read_text().splitlines():
        dig,fn=line.split()
        p=d/fn;name=p.stem
        assert name in expected and name not in seen,(d,name)
        assert p.suffix=='.olean' and sha(p)==dig
        assert sha(work/'imports'/f'{name}.lean')==(d/f'{name}.source.sha256').read_text().split()[0]
        assert not (work/'build'/fn).exists()
        seen.add(name);shutil.copy2(p,work/'build'/fn)
assert seen==expected,(expected-seen,seen-expected)
PY
export LEAN_PATH="$work/build"
(cd "$work/imports"; lean -j 1 -o "$work/build/OneLALongCycle.olean" OneLALongCycle.lean) 2>&1 | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
for n in ('BB6.Agent48OneLAPacked.checked','BB6.Agent48OneLALongCycle.never'):
    match=re.search(r"'"+re.escape(n)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
    if match: used={x.strip() for x in match.group(1).split(',') if x.strip()}
    elif "'"+n+"' does not depend on any axioms" in s: used=set()
    else: raise SystemExit('Missing axiom audit '+n)
    assert used <= {'propext','Classical.choice','Quot.sound'},(n,used)
    print(n,sorted(used))
PY
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/OneLALongCycle.lean" \
  --source-root "$work/imports" --workdir "$work/build" --artifact-dir "$work/build" \
  --manifest-only --manifest "$work/manifest.json" --label raw139-oneLA-packed-cycle \
  --theorem BB6.Agent48OneLALongCycle.never --parent-table '[7,20,11,7,14,1,24,16,2,11,8,4]' \
  --artifact-name raw139-oneLA-packed-cycle-certified --provenance-input "$base/emit-packed-cycle.py"
