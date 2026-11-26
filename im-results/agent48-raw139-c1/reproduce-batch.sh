#!/usr/bin/env bash
set -euo pipefail
# Run from the repository root; accepted producer artifacts are outside the checkout.
base="$PWD/im-results/agent48-raw139-f1-oneRA"
old="$PWD/im-results/agent48-raw139-f1-oneLA"
c1="$PWD/im-results/agent48-raw139-c1"
work="$PWD/.tmp/a48-c1-batch"
export PYTHONPATH="$base:$old"
mkdir -p "$work/imports" "$work/build" "$work/reuse"
python3 - "$work/reuse" "$1" "$2" <<'PY'
import hashlib,json,pathlib,shutil,sys
out=pathlib.Path(sys.argv[1])
records={}
base=None
revisions=set()
for directory,run,claim,bound,code in [
    (sys.argv[2],45689490709,"OneRB",317,7),
    (sys.argv[3],45726436580,"OneLF",232,22)]:
    directory=pathlib.Path(directory)
    paths=list(directory.rglob("manifest.json"))
    assert len(paths)==1, paths
    m=json.loads(paths[0].read_text())
    assert str(m["workflow"]["run_id"])==str(run), m["workflow"]
    assert m["claim"]["theorem"]=="BB6.Agent48Raw139C1"+claim+".all_completions_weighted"
    assert m["claim"]["weighted_bound"]==bound
    assert json.loads(m["claim"]["parent_table"])==[7,24,11,24,14,code,3,16,12,11,24,24]
    if base is None:
        base=m
    else:
        assert m["lean_version"]==base["lean_version"]
        assert m["lean_binary"]["sha256"]==base["lean_binary"]["sha256"]
    revisions.update(m["source_revisions"])
    for row in m["modules"]:
        mod=row["module"]
        if mod in records:
            if row["module_identity_sha256"] != records[mod]["module_identity_sha256"]:
                print("Different accepted identities; consumer will recompile incompatible descendants:",mod)
            continue
        rel=pathlib.Path(row["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        src=paths[0].parent/"build"/rel
        assert hashlib.sha256(src.read_bytes()).hexdigest()==row["olean_sha256"], mod
        dst=out/rel
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(src,dst)
        records[mod]=row
base["modules"]=list(records.values())
base["module_count"]=len(records)
base["source_revisions"]=sorted(revisions)
base["label"]="raw139-c1-two-accepted-producers"
(out/"manifest.json").write_text(json.dumps(base))
print("Accepted producer object candidates:",len(records))
PY
inputs=()
for n in OneLA OneLB OneLF OneRA OneRB OneRF ZeroLB ZeroLF ZeroRB ZeroRC; do
  spec="$c1/spec-$n.json"
  python3 "$c1/package4.py" "$spec" "$work/imports"
  inputs+=(--provenance-input "$spec")
done
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$c1/Raw139C1Batch.lean" --source-root "$work/imports" \
  --workdir "$work/build" --jobs 3 --manifest "$work/manifest.json" \
  --precompiled-manifest "$work/reuse/manifest.json" --precompiled-dir "$work/reuse" \
  --label raw139-c1-twelve-sibling-contract \
  --theorem BB6.Agent48Raw139C1Batch.all_completions_weighted --weighted-bound 2511 \
  --artifact-name raw139-c1-twelve-certified \
  --provenance-input "$c1/package4.py" --provenance-input "$base/blockcert.py" \
  --provenance-input "$base/package.py" --provenance-input "$old/scan.py" \
  --provenance-input "$c1/reproduce-batch.sh" "${inputs[@]}" | tee "$work/log"
python3 - "$work/log" <<'PY'
import re,sys,pathlib
log=pathlib.Path(sys.argv[1]).read_text()
for suffix in ("parents_eq","all_completions_weighted","cover_at","consume"):
    name="BB6.Agent48Raw139C1Batch."+suffix
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log,re.S)
    if m:
        used={x.strip() for x in m.group(1).split(",") if x.strip()}
    elif "'"+name+"' does not depend on any axioms" in log:
        used=set()
    else:
        raise SystemExit("Missing axiom audit "+name)
    assert used <= {"propext","Classical.choice","Quot.sound"}, used
    print(name,sorted(used))
PY
