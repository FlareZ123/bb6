#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-e0sweep-OneLAExtension"
export PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA:$PWD/im-results/agent48-raw139-f1-oneLA"
mkdir -p "$work/imports" "$work/build" "$work/wide-source"
python3 - "$base" "$work" <<'PY'
import pathlib,base64,zlib,sys
base,work=map(pathlib.Path,sys.argv[1:])
(work/'imports/OneLAGrowth.lean').write_bytes(zlib.decompress(base64.b64decode((base/'OneLAGrowth.lean.zlib.b64').read_text())))
PY
tar -xzf im-results/agent1-raw139-e0-oneRD/wide-source.tar.gz -C "$work/wide-source"
python3 "$base/emit-extension.py" "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/OneLAExtension.lean" \
  --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
  --manifest "$work/manifest.json" --label raw139-e0-oneLA-extension \
  --theorem BB6.Agent48Raw139E0OneLAExtension.all_covered \
  --artifact-name raw139-e0sweep-OneLAExtension-certified | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
match=re.search(r"'BB6\.Agent48Raw139E0OneLAExtension\.all_covered' depends on axioms: \[([^\]]*)\]",s,re.S)
assert match and set(x.strip() for x in match.group(1).split(',')) <= {'propext','Classical.choice','Quot.sound'}
PY
