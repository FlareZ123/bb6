"""Reassemble accepted Raw43 proof DAGs for the parent cut, without recompiling every child."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
work = Path(sys.argv[1])
mode = sys.argv[2]
expanded = mode in {"expanded","expandedfive","complete"}
pins = json.loads(os.environ["PINS"])
variants = ["default","0rd","1rd","0re","1re","0rf","1lb","0rc","0lf","1la","1le","1rf","1lf"]
suffixes = {"default":"","0rd":"RD","1rd":"RD1"}
expected = {}
for v in variants:
    suffix = suffixes.get(v, "E"+v.upper())
    spec = json.loads((ROOT/("spec.json" if v=="default" else f"spec_{v}.json")).read_text())
    expected[f"BB6.Agent25Raw43{suffix}.all43child"] = (v,spec.get("bound",75))
if expanded:
    branches = [
        ("b1rc", 382, "BB6.Agent25Raw43B1RC.all_completions"),
        ("b0rc", 620, "BB6.Agent25Raw43B0RC.all_completions"),
        ("b0ra", 390, "BB6.Agent25Raw43B0RA.all_completions"),
    ]
    if mode in {"expandedfive", "complete"}:
        branches += [
            ("b1ra", 519, "BB6.Agent25Raw43B1RA.all_completions"),
            ("b1lb", 289, "BB6.Agent25Raw43B1LB.all_completions"),
        ]
    if mode == "complete":
        branches += [
            ("b0la", 1771, "BB6.Agent25Raw43B0LA.all_completions"),
            ("b1la", 4174, "BB6.Agent25Raw43B1LA.all_completions_full"),
            ("b1le", 11292, "BB6.Agent25Raw43B1LE.all_completions"),
            ("b1re", 4044, "BB6.Agent25Raw43B1RE.all_completions"),
            ("b0le", 3466, "BB6.Agent38Raw43B0LEComplete.all_completions"),
        ]
    for v,b,claim in branches:
        expected[claim] = (v,b)
dest = work/"union"
dest.mkdir(parents=True,exist_ok=True)
entries = {}
seen = set()
base = None
revisions = set()
for pin in pins:
    run,artifact = str(pin["run_id"]),pin["artifact"]
    assert re.fullmatch(r"[0-9]+",run)
    assert re.fullmatch(r"raw43-[a-z0-9-]+-proof",artifact)
    meta = json.loads(subprocess.check_output(["gh","api",f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{run}"]))
    assert meta["conclusion"]=="success" and meta["event"]=="workflow_dispatch"
    assert meta["path"]==".github/workflows/agent10-four-hole.yml"
    d = work/"inputs"/run
    subprocess.run(["gh","run","download",run,"-n",artifact,"-D",str(d)],check=True)
    m = json.loads((d/"manifest.json").read_text())
    claim = m["claim"]["theorem"]
    assert claim in expected,(run,claim)
    v,b = expected[claim]
    assert v not in seen,(run,v,"duplicate accepted variant")
    seen.add(v)
    print("Accepted input",v,run,claim,flush=True)
    assert m["schema_version"]==1
    assert m["workflow"]["run_id"]==run
    assert m["artifact_name"]==artifact
    assert m["proof_source_revision"]==meta["head_sha"]==m["workflow"]["workflow_head_sha"]
    assert m["claim"]["weighted_bound"]==b
    revisions.add(m["proof_source_revision"])
    if base is None: base=m
    assert m["lean_version"]==base["lean_version"]
    assert m["lean_binary"]["sha256"]==base["lean_binary"]["sha256"]
    for e in m["modules"]:
        module=e["module"]
        rel=Path(e["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        obj=d/rel
        assert hashlib.file_digest(obj.open("rb"),"sha256").hexdigest()==e["olean_sha256"],(v,module)
        if module in entries:
            assert entries[module]["module_identity_sha256"]==e["module_identity_sha256"],(v,module,"identity conflict")
        else:
            entries[module]=e
            target=dest/rel
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(obj,target)
assert seen=={v for v,b in expected.values()},("missing variants",{v for v,b in expected.values()}-seen)
merged=dict(base,source_revisions=sorted(revisions),modules=list(entries.values()),
            module_count=len(entries),claim={"theorem":None},label="raw43-parent-inputs",
            roots=[],provenance_inputs=[])
(dest/"manifest.json").write_text(json.dumps(merged,indent=2,sort_keys=True)+"\n")
print("Merged",len(entries),"modules from",len(seen),"accepted closures",flush=True)
if mode != "complete":
    for v in variants:
        subprocess.run([sys.executable,str(ROOT/"generate.py"),v],check=True)
    if expanded:
        for branch,slot,children in [
            ("b1rc","c","0la 0le 0re 1la 1le 1re"),
            ("b0rc","c","0le 0re 1le 1re"),
            ("b0ra","a","0le 0rc 0re 1lb 1le 1re")]+([("b1ra","a","0lc 0le 0rc 0re 1lc 1le 1re"),("b1lb","c","0la 0le 0ra 0re 1la 1le 1ra 1re")] if mode=="expandedfive" else []):
            for v in children.split():
                subprocess.run([sys.executable,str(ROOT/"generate.py"),f"{branch}_{slot}{v}"],check=True)
