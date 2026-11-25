#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-f1-oneRD"
work="$PWD/.tmp/a14-f1-oneRD"
mkdir -p "$work/imports" "$work/build"
base64 -d "$base/../agent14-raw139-f1-oneRF/source.tar.xz.b64" > "$work/oneRF.tar.xz"
base64 -d "$base/source-delta.tar.xz.b64" > "$work/source-delta.tar.xz"
echo "8b87050c5b7088d8e27159fcea9501a4f66999e4382c92e3e039696643d0492e  $work/oneRF.tar.xz" | sha256sum -c
echo "d50cae0d3410b0f52dcbf84242b706b26ff7f9b99bf6fc57a4af85fa8868115f  $work/source-delta.tar.xz" | sha256sum -c
tar -xJf "$work/oneRF.tar.xz" -C "$work/imports" WordShift.lean autopump.py scan.py
tar -xJf "$work/source-delta.tar.xz" -C "$work/imports"
base64 -d "$base/../agent14-raw139-f1-oneLB/source-delta.tar.xz.b64" > "$work/oneLB.tar.xz"
echo "b2d32c975b385cf2ba441ff67ae45aea2c2ff7af64c6be61da84fbc2d5f468b7  $work/oneLB.tar.xz" | sha256sum -c
tar -xJf "$work/oneLB.tar.xz" -C "$work/imports" emitproof.py
(cd "$work/imports"; rm -f pump-*.json; python3 replay.py; python3 chunk.py; sha256sum -c <<'HASHES'
7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf  WordShift.lean
545101fe2a7a74cd294b9e894ea21cb3fb4af433eb17c15b657c9111a9dae81f  Agent14OneRDHard.lean
9e10874098f0674b3c4959db593bd80ee08e02db8a42317ff969b347dc8a51df  Agent14OneRDCover.lean
HASHES
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Agent14OneRDCover.lean" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label raw139-f1-oneRD --theorem BB6.Agent14F1OneRD.all_completions_weighted --parent-table '[7,24,11,24,14,21,3,16,12,11,24,15]' --weighted-bound 489 --artifact-name raw139-f1-oneRD-certified --provenance-input "$base/source-delta.tar.xz.b64" --provenance-input "$base/../agent14-raw139-f1-oneRF/source.tar.xz.b64" --provenance-input "$base/../agent14-raw139-f1-oneLB/source-delta.tar.xz.b64" --provenance-input "$base/reproduce.sh" | tee "$work/log"
python3 - "$work/log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for name in ['BB6.Agent14F1OneRD.checked','BB6.Agent14F1OneRD.all_completions_weighted']:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s)
    assert m and set(m.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'},name
PY
