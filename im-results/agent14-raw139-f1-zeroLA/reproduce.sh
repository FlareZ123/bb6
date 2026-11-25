#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-f1-zeroLA"
work="$PWD/.tmp/a14-f1-zeroLA"
mkdir -p "$work/imports" "$work/build"
base64 -d "$base/../agent14-raw139-f1-oneRF/source.tar.xz.b64" > "$work/oneRF.tar.xz"
base64 -d "$base/source-delta.tar.xz.b64" > "$work/source-delta.tar.xz"
echo "8b87050c5b7088d8e27159fcea9501a4f66999e4382c92e3e039696643d0492e  $work/oneRF.tar.xz" | sha256sum -c
echo "c7a9fbcaac3a8bfb87db80c5fd9e33065ecd1c8c85e939c00141cfd802f6bb4f  $work/source-delta.tar.xz" | sha256sum -c
tar -xJf "$work/oneRF.tar.xz" -C "$work/imports" WordShift.lean autopump.py scan.py emitproof.py
tar -xJf "$work/source-delta.tar.xz" -C "$work/imports"
(cd "$work/imports"; rm -f pump-*.json; python3 replay.py; python3 gencarry.py; python3 chunk.py; sha256sum -c <<'HASHES'
7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf  WordShift.lean
b11a441fccca78e0cba65657a39bd36e581f998be97314e221271135b2c39e37  LAOuter.lean
1f96d23975885ab07e7d78692ab818333ec207c9eb0a335e953ef70749ff7b82  LACarry.lean
465b2dae949b5f4e92137263365fc61f988b278e97314b7caaa58343490fbdef  Agent14OneLAHard.lean
b8b2b30f870210b1b153c0207f660b1c25811f069bbecf42e36d0d12cbe9e16e  Agent14OneLACover.lean
HASHES
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Agent14OneLACover.lean" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label raw139-f1-zeroLA --theorem BB6.Agent14F1OneLA.all_completions_weighted --parent-table '[7,24,11,24,14,21,3,16,12,11,24,0]' --weighted-bound 553 --artifact-name raw139-f1-zeroLA-certified --provenance-input "$base/source-delta.tar.xz.b64" --provenance-input "$base/../agent14-raw139-f1-oneRF/source.tar.xz.b64" --provenance-input "$base/reproduce.sh" | tee "$work/log"
python3 - "$work/log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for name in ['BB6.Agent14F1OneLA.checked','BB6.Agent14F1OneLA.all_completions_weighted']:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s)
    assert m and set(m.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'},name
PY
