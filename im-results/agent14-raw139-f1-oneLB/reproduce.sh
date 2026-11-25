#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-f1-oneLB"
work="$PWD/.tmp/a14-f1-oneLB"
mkdir -p "$work/imports" "$work/build"
base64 -d "$base/../agent14-raw139-f1-oneRF/source.tar.xz.b64" > "$work/oneRF.tar.xz"
base64 -d "$base/source-delta.tar.xz.b64" > "$work/source-delta.tar.xz"
echo "8b87050c5b7088d8e27159fcea9501a4f66999e4382c92e3e039696643d0492e  $work/oneRF.tar.xz" | sha256sum -c
echo "b2d32c975b385cf2ba441ff67ae45aea2c2ff7af64c6be61da84fbc2d5f468b7  $work/source-delta.tar.xz" | sha256sum -c
tar -xJf "$work/oneRF.tar.xz" -C "$work/imports" WordShift.lean autopump.py scan.py
tar -xJf "$work/source-delta.tar.xz" -C "$work/imports"
(cd "$work/imports"; rm -f pump-*.json; python3 replay.py; python3 chunk.py; sha256sum -c <<'HASHES'
7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf  WordShift.lean
359a5ec5e3705158d8d78b3225c5304f4bf3599297c9834dc723b70fd578c266  LBOuter.lean
0856337e7594a41d5435bd332ade5c9ce38566e5b07ff1565619cb5d9edc3aee  LBCarry.lean
b5ac0ec59b778eb587be9ad9568c585aa842dabbd0e7b09845446045cf715042  Agent14OneLBHard.lean
a31688ac0ccccaaa492f806cf2bb9dad0a52ec8b56ceaf99b21d3d298d78a42a  Agent14OneLBCover.lean
HASHES
)
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Agent14OneLBCover.lean" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label raw139-f1-oneLB --theorem BB6.Agent14F1OneLB.all_completions_weighted --parent-table '[7,24,11,24,14,21,3,16,12,11,24,6]' --weighted-bound 172 --artifact-name raw139-f1-oneLB-certified --provenance-input "$base/source-delta.tar.xz.b64" --provenance-input "$base/../agent14-raw139-f1-oneRF/source.tar.xz.b64" --provenance-input "$base/reproduce.sh" | tee "$work/log"
python3 - "$work/log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for name in ['BB6.Agent14F1OneLB.checked','BB6.Agent14F1OneLB.all_completions_weighted']:
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s)
    assert m and set(m.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'},name
PY
