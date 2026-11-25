#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-f1-oneRF"
work="$PWD/.tmp/a14-f1-oneRF"
mkdir -p "$work/imports" "$work/build"
base64 -d "$base/source.tar.xz.b64" > "$work/source.tar.xz"
echo "8b87050c5b7088d8e27159fcea9501a4f66999e4382c92e3e039696643d0492e  $work/source.tar.xz" | sha256sum -c
tar -xJf "$work/source.tar.xz" -C "$work/imports"
(cd "$work/imports"; rm -f pump-*.json; python3 replay.py; python3 chunk.py; sha256sum -c <<'HASHES'
7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf  WordShift.lean
2cb41161279c8eaec09cc89030634f77c6da5d6ddacd590aedfa225a442c078b  RunCarry.lean
3bdf42ec78668cfa36707f3ca31bcafdc6a32ca1f918710fce414b9412037cc7  FastQuery.lean
075d364b997245763ad33de079f3b9f34c44c993b112930432a50e4b10fc3bb3  Agent14OneRFHard.lean
b94cb7678d30cf3521b3e3eed19181019878101f50c901f675035d9031bf58a2  Agent14OneRFCover.lean
HASHES
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Agent14OneRFCover.lean" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label raw139-f1-oneRF --theorem BB6.Agent14F1OneRF.all_completions_weighted --parent-table '[7,24,11,24,14,21,3,16,12,11,24,23]' --weighted-bound 5423 --artifact-name raw139-f1-oneRF-certified --provenance-input "$base/source.tar.xz.b64" --provenance-input "$base/reproduce.sh" | tee "$work/log"
python3 - "$work/log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for name in ['BB6.Agent14F1OneRF.checked','BB6.Agent14F1OneRF.all_completions_weighted']:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s)
    assert m and set(m.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'},name
PY
