#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-f1-oneLA"
work="$PWD/.tmp/a48-f1-oneLA"
mkdir -p "$work/imports" "$work/build"
(
  cd "$work/imports"
  cp "$base/recipes.txt" .
  python3 "$base/replay.py"
  python3 "$base/package.py"
  echo '0efe6d872460d07282eaa1cb63d878c211b426a2da8cb70a3bb1675d3e69a730  ChampionF1OneLACover.lean' | sha256sum -c
  echo '4d4f583f5f3197d2d12bed38aeea081fc8f1f74c7f8af9856ffaded24e9e5dbf  ChampionF1OneLAHard.lean' | sha256sum -c
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$work/imports/ChampionF1OneLACover.lean" \
  --workdir "$work/build" --jobs 4 \
  --manifest "$work/manifest.json" --label raw139-f1-oneLA \
  --theorem BB6.Agent48F1OneLA.all_completions_weighted \
  --parent-table '[7,24,11,24,14,21,3,16,12,11,24,2]' \
  --weighted-bound 290 --artifact-name raw139-f1-oneLA-certified \
  --provenance-input "$base/recipes.txt" \
  --provenance-input "$base/scan.py" \
  --provenance-input "$base/autopump.py" \
  --provenance-input "$base/emitproof.py" \
  --provenance-input "$base/replay.py" \
  --provenance-input "$base/package.py" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
names = ['BB6.Agent48F1OneLA.checked','BB6.Agent48F1OneLA.all_completions_weighted']
names += [f'BB6.Agent48OneLA.H{i}.{s}' for i in range(26) if i != 7 for s in ('growth','never')]
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
