#!/usr/bin/env bash
set -euo pipefail
repo="$(pwd)"
base="$repo/im-results/agent3-raw139-e0-zeroRA"
out="/tmp/a3e0-prepared"
mkdir -p "$out"
test -f /tmp/a3-c1/manifest.json
python - <<'PY'
import json
j=json.load(open('/tmp/a3-c1/manifest.json'))
assert j['claim']['theorem']=='BB6.Agent48Raw139C1Batch.all_completions_weighted'
assert j['claim']['weighted_bound']==2511
PY
cp -r /tmp/a3-c1/build "$out/build"
export A3_BUILD="$out/build"
export LEAN_PATH="$A3_BUILD"
cd "$base"
echo "fb2d8506761f3a7843e59d16202ad069f68fba835dca9e5b03fe46623dd58b7d  source.tar.xz" | sha256sum -c
# The source bundle predates the checked fast certificate; preserve the current
# working-tree driver and compressed source while extracting the older bundle.
cp fast.py /tmp/a3-e0-fast.py
cp Agent3PackedFast.lean.xz /tmp/a3-e0-fast.lean.xz
tar -xJf source.tar.xz
cp /tmp/a3-e0-fast.py fast.py
cp /tmp/a3-e0-fast.lean.xz Agent3PackedFast.lean.xz
echo "56b716777e9b1371b4638d7f4e54e0d0812ad5f2618793a43bb9e88633073b7e  Agent3PackedFast.lean.xz" | sha256sum -c
python fast.py
cp Agent3PackedAudit.lean Agent3PackedFast.lean "$A3_BUILD"
cd "$repo"
sha256sum -c <<'EOF'
46d74ebad141d7123d2921086becf7ce42658ae05f010f0862c579c103231b27  im-results/agent50-weighted-tnf-pilot/SparseZipper.lean
346daa8772700ee235c8342a1128153c43317dd1724e8f95b5e004e50fbd732f  im-results/agent31-three-hole-tnf/SweepPumping.lean
86e3e32d8f4ba84346ff2fd168135d46ed402c2b440a1d986e07233b3dbf6ca1  im-results/agent10-tnf-multipump/ZipAuditCore.lean
EOF
cp im-results/agent50-weighted-tnf-pilot/SparseZipper.lean im-results/agent31-three-hole-tnf/SweepPumping.lean im-results/agent10-tnf-multipump/ZipAuditCore.lean "$A3_BUILD"
cd "$A3_BUILD"
for m in SparseZipper SweepPumping ZipAuditCore Agent3PackedAudit Agent3PackedFast; do
 lean -o "$m.olean" "$m.lean"
done
cd "$base"
g++ -O3 -std=c++17 census.cpp -o census
./census 1 | tee counts1.txt
python classify.py
cp counts1.txt recipes.jsonl "$out/"
python long.py
cd "$A3_BUILD"
lean -o A3E0RALongBase.olean A3E0RALongBase.lean
for f in A3E0RALongPart*.lean A3E0RALongJoin*.lean A3E0RALongCover.lean; do
 lean -o "${f%.lean}.olean" "$f"
done
