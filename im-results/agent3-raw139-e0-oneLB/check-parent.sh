#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent3-raw139-e0-oneLB"
work="$PWD/.tmp/a3-oneLB-parent"
mkdir -p "$work/imports" "$work/build" "$work/reuse" /tmp/oneLB-banks
readarray -t ids < <(python3 - "$base/child-banks.json" <<'PY'
import json,sys
for run,artifact in json.load(open(sys.argv[1])).values():print(artifact)
PY
)
for id in "$@"; do ids+=("$id"); done
dirs=()
for id in "${ids[@]}"; do
  [[ "$id" =~ ^[0-9]+$ ]]
  mkdir -p "/tmp/oneLB-banks/$id"
  gh api "repos/$GITHUB_REPOSITORY/actions/artifacts/$id/zip" > "/tmp/oneLB-banks/$id.zip"
  unzip -q "/tmp/oneLB-banks/$id.zip" -d "/tmp/oneLB-banks/$id"
  dirs+=("/tmp/oneLB-banks/$id")
done
python3 "$base/merge-bank.py" "$work/reuse" "$work/imports" "${dirs[@]}"
python3 "$base/emit-parent.py" "$work/imports" "${dirs[@]}"
root=ParentPartial
claim=parent_cover
if [[ -f "$work/imports/ParentAssembly.lean" ]]; then root=ParentAssembly; claim=all_completions_weighted; fi
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/$root.lean" \
 --source-root "$work/imports" --workdir "$work/build" --jobs 3 \
 --override RootShift=im-results/agent8-coverage-contract/RootShift.lean \
 --override SparseZipper=im-results/agent50-weighted-tnf-pilot/SparseZipper.lean \
 --override Symmetry=im-results/agent8-coverage-contract/Symmetry.lean \
 --override Frontier=im-results/agent8-coverage-contract/Frontier.lean \
 --precompiled-manifest "$work/reuse/manifest.json" --precompiled-dir "$work/reuse" \
 --manifest "$work/manifest.json" --label raw139-OneLB-$root \
 --theorem "BB6.Agent3OneLBParent.$claim" --parent-table '[7,24,11,24,14,24,24,16,6,11,24,24]' \
 --weighted-bound 187672026 --artifact-name raw139-OneLB-$root-certified \
 --provenance-input "$base/child-banks.json" --provenance-input "$base/emit-parent.py" | tee "$work/log"
python3 - "$work/log" "$claim" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
for t in {sys.argv[2],"parent_cover"}:
 name="BB6.Agent3OneLBParent."+t
 m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",s,re.S)
 if m:used={x.strip() for x in m.group(1).split(",") if x.strip()}
 elif "'"+name+"' does not depend on any axioms" in s:used=set()
 else:raise SystemExit("Missing axiom audit: "+name)
 assert used<={"propext","Classical.choice","Quot.sound"},(name,used)
 print(name,sorted(used))
PY
