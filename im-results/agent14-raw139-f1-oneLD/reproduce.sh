#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-f1-oneLD"
work="$PWD/.tmp/a14-f1-oneLD"
mkdir -p "$work/imports" "$work/build"
(
  cd "$work/imports"
  rm -f pump-*.json
  cp "$base/recipes.txt" .
  rm -f Agent14OneLDCarry.lean
  python3 "$base/replay.py"
  python3 "$base/package.py"
  echo "24d2b82d1c9a11c33b28ab9e7fb460ce2b9ea05db919dd6840d4ebceb76bf34a  $base/Agent14OneLDCarry.lean" | sha256sum -c
  echo "b436a77405c29314f7f75e9d773326591f7eeb8ad7098b6b854b93afa83818d0  Agent14OneLDHard.lean" | sha256sum -c
  echo "c1e905c2103d30b39bac253c5015f5a51da87aa57c6c5c9acd35e677e022f225  Agent14OneLDCover.lean" | sha256sum -c
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$work/imports/Agent14OneLDCover.lean" \
  --workdir "$work/build" --jobs 4 \
  --manifest "$work/manifest.json" --label raw139-f1-oneLD \
  --theorem BB6.Agent14F1OneLD.all_completions_weighted \
  --parent-table '[7,24,11,24,14,21,3,16,12,11,24,14]' \
  --weighted-bound 264 --artifact-name raw139-f1-oneLD-certified \
  --provenance-input "$base/recipes.txt" \
  --provenance-input "$base/Agent14OneLDCarry.lean" \
  --provenance-input "$base/replay.py" \
  --provenance-input "$base/package.py" \
  --provenance-input "$base/../agent48-raw139-f1-oneLA/scan.py" \
  --provenance-input "$base/../agent48-raw139-f1-oneLA/autopump.py" \
  --provenance-input "$base/../agent48-raw139-f1-oneLA/emitproof.py" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
log=pathlib.Path(sys.argv[1]).read_text()
names=['BB6.Agent14F1OneLD.checked','BB6.Agent14F1OneLD.all_completions_weighted','BB6.Agent14OneLD.H25.carry']
names += [f'BB6.Agent14OneLD.H{i}.{s}' for i in range(32) for s in ('growth','never')]
for name in names:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log,re.S)
    if m: used={x.strip() for x in m.group(1).split(',') if x.strip()}
    elif "'"+name+"' does not depend on any axioms" in log: used=set()
    else: raise SystemExit('Missing audit: '+name)
    assert used <= {'propext','Classical.choice','Quot.sound'}, (name,used)
    print(name,sorted(used))
PY
