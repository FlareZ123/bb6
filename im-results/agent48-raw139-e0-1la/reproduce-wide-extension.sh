#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-e0sweep-OneLAWide"
mkdir -p "$work/imports" "$work/build"
python3 "$base/emit-wide-extension.py" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/OneLAWide.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-oneLA-wide \
  --theorem BB6.Agent48OneLAWide.never \
  --artifact-name raw139-e0sweep-OneLAWide-certified | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
m=re.search(r"'BB6\.Agent48OneLAWide\.never' depends on axioms: \[([^\]]*)\]",s,re.S)
assert m and set(x.strip() for x in m.group(1).split(',')) <= {'propext','Classical.choice','Quot.sound'}
PY
