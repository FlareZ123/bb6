#!/usr/bin/env bash
set -euo pipefail
kind="$1"
name="$2"
[[ "$name" =~ ^(Zero|One)[LR][A-F]$ ]]
base="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
c1="$PWD/im-results/agent48-raw139-c1"
export PYTHONPATH="$base:$old"
case "$kind" in
  f1) [[ "$name" == OneRA ]]; spec="$base/blocks.json"; gen="$base/package.py"; prefix=ChampionF1OneRA; ns=BB6.Agent48F1OneRA;;
  c1) spec="$c1/spec-$name.json"; gen="$c1/package4.py"; prefix="Raw139C1$name"; ns="BB6.Agent48Raw139C1$name";;
  *) exit 2;;
esac
work="$PWD/.tmp/a48-$kind-$name"
mkdir -p "$work/imports" "$work/build"
python3 "$gen" "$spec" "$work/imports"
read -r bound parent < <(python3 - "$spec" <<'PY'
import json,sys
s=json.load(open(sys.argv[1]))
print(s['bound'],json.dumps(s['parent'],separators=(',',':')))
PY
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$work/imports/$(echo "$prefix")Cover.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label "raw139-$kind-$name" \
  --theorem "$ns.all_completions_weighted" \
  --parent-table "$parent" --weighted-bound "$bound" --artifact-name "raw139-$kind-$name-certified" \
  --provenance-input "$spec" --provenance-input "$gen" \
  --provenance-input "$base/blockcert.py" --provenance-input "$base/package.py" \
  --provenance-input "$old/scan.py" | tee "$work/log"
python3 - "$work/log" "$ns" <<'PY'
import re,sys,pathlib
log=pathlib.Path(sys.argv[1]).read_text()
name=sys.argv[2]+'.all_completions_weighted'
m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log,re.S)
if m:
    used={x.strip() for x in m.group(1).split(',') if x.strip()}
elif "'"+name+"' does not depend on any axioms" in log:
    used=set()
else: raise SystemExit('Missing axiom audit '+name)
assert used <= {'propext','Classical.choice','Quot.sound'}, used
print(name,sorted(used))
PY
