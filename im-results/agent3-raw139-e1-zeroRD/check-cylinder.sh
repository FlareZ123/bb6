#!/usr/bin/env bash
set -euo pipefail
kind="$1"
base="$PWD/im-results/agent3-raw139-e1-zeroRD"
work="$PWD/.tmp/a3-e1-$kind"
mkdir -p "$work/imports" "$work/reuse" "$work/build" /tmp/a3-e1-core
if [[ "$kind" == E1D0Leaf2265Core ]]; then
  lean -o "$work/build/Leaf2265Core.olean" "$base/Leaf2265Core.lean" 2>&1 | tee "$work/log"
  LEAN_PATH="$work/build" lean -o "$work/build/Leaf2265Compress.olean" "$base/Leaf2265Compress.lean" 2>&1 | tee -a "$work/log"
  node "$base/emit-2265.cjs" > "$work/imports/Leaf2265Trace.lean"
  LEAN_PATH="$work/build" lean -o "$work/build/Leaf2265Trace.olean" "$work/imports/Leaf2265Trace.lean" 2>&1 | tee -a "$work/log"
fi
python3 im-results/agent13-coverage/unpack.py
gh api "repos/$GITHUB_REPOSITORY/actions/artifacts/15175093456/zip" > /tmp/a3-e1-core.zip
unzip -q /tmp/a3-e1-core.zip -d /tmp/a3-e1-core
python3 im-results/agent3-raw139-e0-oneLB/merge-bank.py "$work/reuse" "$work/imports" /tmp/a3-e1-core
if [[ "$kind" == E1D0Leaf2265Core ]]; then
  cp "$base"/Leaf2265{Core,Compress,Bridge}.lean "$work/imports/"
  export LEAN_PATH="$work/build:$work/reuse"
  lean -o "$work/build/Leaf2265Bridge.olean" "$work/imports/Leaf2265Bridge.lean" 2>&1 | tee -a "$work/log"
  python3 - "$work/log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for t in ["BB6.Agent3Leaf2265.terminalRun","BB6.Agent3Leaf2265.terminalRead","BB6.Agent3Leaf2265Bridge.reached","BB6.Agent3Leaf2265Bridge.weighted"]:
 m=re.search(r"'"+re.escape(t)+r"' depends on axioms: \[([^\]]*)\]",s)
 if m: used={x.strip() for x in m.group(1).split(",") if x.strip()}
 elif "'"+t+"' does not depend on any axioms" in s: used=set()
 else: raise SystemExit("Missing axiom audit: "+t)
 assert used<={"propext","Classical.choice","Quot.sound"},(t,used)
 print(t,sorted(used))
PY
  printf '%s\n' '{"scope":"original-source weighted cover","theorem":"BB6.Agent3Leaf2265Bridge.weighted","parent_table":[7,20,11,1,14,11,22,16,24,13,2,12]}' > "$work/manifest.json"
  exit 0
fi
if [[ "$kind" == E1D0CounterCarry ]]; then
  python3 tools/lean_compile_closure.py "$base/CounterCarryBridge.lean" \
    --source-root "$work/imports" --workdir "$work/build" --jobs 2 \
    --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
    --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
    --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
    --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
    --precompiled-manifest "$work/reuse/manifest.json" --precompiled-dir "$work/reuse" \
    --manifest "$work/manifest.json" --label "$kind" \
    --theorem BB6.Agent3CounterCarry.never --artifact-name raw139-E1D0CounterCarry-certified \
    --provenance-input "$base/CounterCarry.lean" --provenance-input "$base/CounterCarryBridge.lean" | tee "$work/log"
  python3 - "$work/log" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for name in ["CounterCarry.increment","CounterCarry.never","BB6.Agent3CounterCarry.never","BB6.Agent3CounterCarry.weighted"]:
 m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
 if m: used={x.strip() for x in m.group(1).split(",") if x.strip()}
 elif "'"+name+"' does not depend on any axioms" in s: used=set()
 else: raise SystemExit("Missing axiom audit: "+name)
 assert used<={"propext","Classical.choice","Quot.sound"},(name,used)
 print(name,sorted(used))
PY
  exit 0
fi
limit=450
case "$kind" in
E1D0ZeroRF) d=21; emitter=emit-d0rf0.py; recipes=census-d0rf0.json; hash=; suffix=ZeroRF; B=394; limit=140;;
E1D0ZeroLE) d=16; emitter=emit-d0le.py; recipes=recipes-d0le.json; hash=ee587f95632ca2d9a914f9777ab7243061396a6e5edb0e7f973178365be70a4b; suffix=ZeroLE; B=456;;
E1D0ZeroLA) d=0; emitter=emit-d0la.py; recipes=recipes-d0la.json; hash=badd35612f9653ed71106e91dde892cbe7dbf4072da92663cd49549eb7af49d1; suffix=ZeroLA; B=4653;;
E1D0ZeroRD) d=13; emitter=emit-d0rd.py; recipes=recipes-d0rd.json; hash=3bef0ba1d4b421a915b4ff650622f11aa78c8ad71710a226b206a26fa0fd6127; suffix=ZeroRD; B=679;;
E1D0OneRB) d=7; emitter=emit-d0rb1.py; recipes=recipes-d0rb1.json; hash=b6d3c1914722160084d71c5631f0dd344943d0c985b45cbfb8827851e8b75ce5; suffix=OneRB; B=435;;
E1D0ZeroRE) d=17; emitter=emit.py; recipes=recipes.json; hash=3d69cf3e91812cebf72213a743adbf463e7d0bfd8733092ccaec1bc06315b2a6; suffix=ZeroRE; B=533;;
*) exit 2;;
esac
g++ -std=c++17 -O3 im-results/agent48-raw139-e0-0re/replay.cpp -o "$work/replay"
"$work/replay" "$limit" 2 7 24 11 24 14 24 "$d" 16 24 13 24 24 > "$work/partition.json"
if [[ -n "$hash" ]]; then echo "$hash  $work/partition.json" | sha256sum -c -; fi
export PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA"
if [[ "$kind" == E1D0ZeroRE ]]; then
 python3 "$base/$emitter" "$work/partition.json" "$base/$recipes" "$work/imports" 600
else
 python3 "$base/$emitter" "$work/partition.json" "$work/imports" 600
fi
if [[ "$kind" == E1D0ZeroLE || "$kind" == E1D0ZeroRF ]]; then
  # Closure resolver must see original, checked ray/reflect definitions.
  cp "$base"/UnaryGrow{,Bridge,Reflect}.lean "$work/imports/"
fi
root="A3E1ZeroRDD0${suffix}Cover"
ns="BB6.Agent3Raw139E1ZeroRDD0${suffix}"
python3 tools/lean_compile_closure.py "$work/imports/$root.lean" \
 --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
 --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
 --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
 --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
 --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
 --override PackedPrefixAudit=im-results/agent48-prefix-audit/PackedPrefixAudit.lean \
 --precompiled-manifest "$work/reuse/manifest.json" --precompiled-dir "$work/reuse" \
 --manifest "$work/manifest.json" --label "$kind" \
 --theorem "$ns.weighted" --parent-table "[7,24,11,24,14,24,$d,16,24,13,24,24]" \
 --weighted-bound "$B" --artifact-name "raw139-$kind-certified" \
 --provenance-input "$base/$recipes" --provenance-input "$base/$emitter" | tee "$work/log"
python3 - "$work/log" "$ns" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for t in ["hRoot","weighted","all_completions_weighted"]:
 name=sys.argv[2]+"."+t
 m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
 if m: used={x.strip() for x in m.group(1).split(",") if x.strip()}
 elif "'"+name+"' does not depend on any axioms" in s: used=set()
 else: raise SystemExit("Missing axiom audit: "+name)
 assert used<={"propext","Classical.choice","Quot.sound"},(name,used)
 print(name,sorted(used))
PY
