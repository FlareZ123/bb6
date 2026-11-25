#!/usr/bin/env bash
set -euo pipefail
name="$1"
if [[ "$name" == OneRA ]]; then
  exec bash im-results/agent48-raw139-f1-oneRA/reproduce-blocks.sh f1 OneRA
fi
[[ "$name" =~ ^(Zero|One)[LR][A-F]$ ]]
base="$PWD/im-results/agent48-raw139-f1-oneLA"
spec="$base/spec-$name.json"
work="$PWD/.tmp/a48-f1-$name"
mkdir -p "$work/imports" "$work/build"
read -r code bound cover_hash hard_hash < <(python3 - "$spec" <<'PY'
import json,sys
s=json.load(open(sys.argv[1]))
print(s['code'],s['bound'],s['cover_sha'],s['hard_sha'])
PY
)
(
  cd "$work/imports"
  cp "$base/recipes-$name.txt" recipes.txt
  python3 "$base/replay-sibling.py" "$spec"
  python3 "$base/package-sibling.py" "$spec"
  echo "$cover_hash  ChampionF1${name}Cover.lean" | sha256sum -c
  echo "$hard_hash  ChampionF1${name}Hard.lean" | sha256sum -c
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$work/imports/ChampionF1${name}Cover.lean" \
  --workdir "$work/build" --jobs 4 \
  --manifest "$work/manifest.json" --label "raw139-f1-$name" \
  --theorem "BB6.Agent48F1${name}.all_completions_weighted" \
  --parent-table "[7,24,11,24,14,21,3,16,12,11,24,$code]" \
  --weighted-bound "$bound" --artifact-name "raw139-f1-$name-certified" \
  --provenance-input "$spec" \
  --provenance-input "$base/recipes-$name.txt" \
  --provenance-input "$base/scan.py" \
  --provenance-input "$base/autopump.py" \
  --provenance-input "$base/emitproof.py" \
  --provenance-input "$base/replay-sibling.py" \
  --provenance-input "$base/package-sibling.py" | tee "$work/log"
python3 - "$work/log" "$spec" <<'PY'
import pathlib, re, sys,json
log = pathlib.Path(sys.argv[1]).read_text()
s=json.load(open(sys.argv[2]));name=s['name']
names = [f'BB6.Agent48F1{name}.checked',f'BB6.Agent48F1{name}.all_completions_weighted']
names += [f'BB6.Agent48{name}.H{i}.{t}' for i in range(s['counts']['open']) if str(i) not in s['far_overrides'] for t in ('growth','never')]
for name in names:
    match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log, re.S)
    if match:
        used = {x.strip() for x in match.group(1).split(',') if x.strip()}
    elif "'" + name + "' does not depend on any axioms" in log:
        used = set()
    else:
        raise SystemExit('Missing audit: ' + name)
    assert used <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, used)
    print(name, sorted(used))
PY
