#!/usr/bin/env python3
"""Kernel-link the eleven independently source-accepted Raw39 first-hole bounds.

This is an integration runner, never a replacement for independent producer
source checks. Each pinned GitHub Actions ZIP is SHA-256 authenticated, its CI
run revision/status is checked, and its transitive Lean objects are checked
against the producer manifest before duplicate identities are compared.
Successful compilation of Raw39CompleteJoin against this combined environment
is the decisive source-connected parent proof; no result is claimed prior to it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
sys.path.insert(0, str(REPO / "im-results/agent31-shared-core"))
import assemble_canonical68 as a68

# branch, run, artifact, ZIP digest, producer head, artifact name, weighted bound.
PINS = [
 ("1RB",45639153728,15036330602,"7ecef8579cfb93f574126da721eda176f172a6628ee669927b8d69f624e688d0","439ff1526b1d9b19b3e5a02f8c1c764eadcbdbda","raw39-partial-parent-proof",175),
 ("0RB",45644271619,15039311430,"ee9783033b2e90c319d2829b64c8ca20b16447a16d898e58a1b13fb94f95bd26","c39dbcb430765b7d8f630dc7fd7633e613bee8e6","raw39-0RB-partial-parent-proof",1271),
 ("1RC",45644280485,15039350734,"d1df2e9297455e4bd3da78868061c1b04254291eea39c9a6cc48b50dddcb9c66","c39dbcb430765b7d8f630dc7fd7633e613bee8e6","raw39-1RC-partial-parent-proof",1882),
 ("0RE",45680199670,15054707946,"c3c3abedb96b1f0eba3ebc60f52a4d8048c148c52e677f6b7ae1e044768c9798","9e3bfe908a91b42031d33e46c42b03c71b1a84b1","raw39-0RE-partial-parent-proof",944),
 ("0RC",45753648611,15087393537,"2c085341ac516ae6b8e40796c96e77d77aa974fc97a79ffef508f5f57925d7d1","aa832e9f7734b28505baa8527de0f19979f009ca","raw39-0RC-partial-parent-proof",2354),
 ("0LA",45766252232,15091944603,"d0a7a4bc52c65f54fe386efc077ac56635becbf0af02d69dd7c57dc97da64942","a82f9d0ca7b85b6dfb2b32e09d6d36c1e8133680","raw39-0LA-semantic-proof",1003),
 ("1LB",45796346387,15105668345,"e9cb3111213eaf4abdf9ec37ba22cc3a3cf54cf0628f7ad0cc755aa2220619dc","71a9e95c80f388f8889b183cc9474ba3833a10a4","raw39-1LB-semantic-proof",266),
 ("1LA",45796691482,15105938864,"b8b6287eec281e1764267b438dde79de430ea87e958cef4dfaf9b65ae7a61c80","09d6ed0777264e83a08fade7284edf49445bbb57","raw39-1LA-semantic-proof",349),
 ("1RE",45799903269,15109002717,"5373b9a16d92ccf716894dec79fa7d2a5220af91d392f55b3cfa30bd523921f0","f24ca0ced242de3e13e71f6cf9cc970fb637340d","raw39-1RE-semantic-proof",1459),
 ("0LE",46093979153,15244454609,"5ef920579ad1bd8187a1ca291c132610af7186adde0e3d8efab1f8f277ac1c28","ca7f3b0ed9824a27f7b8991638423b524c01de58","raw39-0LE-semantic-proof",15125),
]
ALLOW = {"propext","Classical.choice","Quot.sound"}
THEOREMS = [
 "BB6.Agent11Raw39Closed.zeroLE_bound",
 "BB6.Agent11Raw39Closed.oneLE_bound",
 "BB6.Agent11Raw39Closed.parent_bound",
 "BB6.Agent11Raw39Closed.parent_cover",
 "BB6.Agent11Raw39Closed.parent_exact",
 "BB6.Agent11Raw39Closed.parent_attained",
]

def check(cond, msg):
    if not cond:
        raise RuntimeError(msg)

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def dynamic_pin(run_id):
    run=a68.api_json(f"repos/{a68.REPO}/actions/runs/{run_id}")
    check(run["status"]=="completed" and run["conclusion"]=="success",
          f"1LE producer not successful: {run_id}: {run['status']}/{run['conclusion']}")
    arts=a68.api_json(f"repos/{a68.REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    matches=[a for a in arts if a["name"]=="raw39-1LE-semantic-proof" and not a["expired"]]
    check(len(matches)==1, f"exactly one complete 1LE proof expected: {matches}")
    a=matches[0]
    check(a["digest"].startswith("sha256:"), "missing GitHub artifact digest")
    return ("1LE",run_id,a["id"],a["digest"][7:],run["head_sha"],a["name"],28311)

def gather(pin, work, compiler_sha, compiler_version):
    branch,run_id,aid,ziphash,revision,name,B=pin
    run=a68.api_json(f"repos/{a68.REPO}/actions/runs/{run_id}")
    check(run["status"]=="completed" and run["conclusion"]=="success",
          f"{branch} source producer failed: {run_id}")
    check(run["head_sha"]==revision, f"{branch}: wrong source revision")
    info=a68.api_json(f"repos/{a68.REPO}/actions/artifacts/{aid}")
    check(info["name"]==name and info["workflow_run"]["id"]==run_id,
          f"{branch}: wrong producer artifact")
    check(info["digest"]=="sha256:"+ziphash and not info["expired"],
          f"{branch}: unpinned/expired archive")
    dirs=a68.download((aid,run_id,ziphash),work)
    metadata=work/"metadata"/str(aid)
    matches=[]
    for p in metadata.rglob("manifest.json"):
        j=json.loads(p.read_text())
        if j.get("artifact_name")==name:
            matches.append(j)
    check(len(matches)==1,f"{branch}: expected one named source manifest, found {len(matches)}")
    manifest=matches[0]
    check(manifest["schema_version"]==1, f"{branch}: unexpected manifest schema")
    check(manifest["proof_source_revision"]==revision,
          f"{branch}: source manifest revision mismatch")
    check(manifest["lean_version"]==compiler_version and
          manifest["lean_binary"]["sha256"]==compiler_sha,
          f"{branch}: nonidentical Lean compiler")
    mods=manifest["modules"]
    allowed={m["module"]+".olean":m for m in mods}
    check(len(allowed)==manifest["module_count"]==len(mods),
          f"{branch}: duplicated modules")
    observed={}
    for d in dirs:
        for p in d.glob("*.olean"):
            check(p.name not in observed,f"{branch}: duplicate object {p.name}")
            observed[p.name]=p
    check(set(observed)==set(allowed),
          f"{branch}: missing or unclaimed object names {set(observed)^set(allowed)}")
    for name,p in observed.items():
        m=allowed[name]
        check(m["olean_sha256"]==digest(p), f"{branch}: bad object digest for {name}")
        check(set(m["project_imports"]) <= {x["module"] for x in mods},
              f"{branch}: incomplete original source closure for {name}")
    claim=manifest.get("claim") or {}
    if "weighted_bound" in claim:
        check(claim["weighted_bound"]==B,
              f"{branch}: incorrect weighted bound in producer manifest")
    check(manifest["roots"],f"{branch}: missing source roots")
    return observed,manifest

def source_index():
    index={}
    for p in REPO.glob("im-results/**/*.lean"):
        index.setdefault(p.stem,[]).append(p)
    for p in REPO.glob("tools/**/*.lean"):
        index.setdefault(p.stem,[]).append(p)
    return index

def compile_missing(module,linked,evidence,index,busy,compiled):
    if (linked/(module+".olean")).is_file():
        return
    check(module not in busy,f"cyclic source imports: {module}")
    if module.startswith(("Init.","Lean.","Std.","Mathlib.")) or module in ("Init","Lean","Std"):
        return
    matches=index.get(module,[])
    check(matches,f"no trusted source for missing module {module}")
    if len(matches)>1:
        select=[p for p in matches if p.parent==ROOT]
        if module=="ExactAuditWeight":
            select=[p for p in matches if p.parent.name=="agent10-tnf-multipump"]
        check(len(select)==1,
              f"ambiguous missing import {module}: {matches}")
        path=select[0]
    else:
        path=matches[0]
    busy.add(module)
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            for dep in line[7:].split():
                compile_missing(dep,linked,evidence,index,busy,compiled)
    busy.remove(module)
    obj=linked/(module+".olean")
    env=dict(os.environ,LEAN_PATH=str(linked))
    log=evidence/(module+".log")
    with log.open("wb") as output:
        p=subprocess.run(["lean","-o",str(obj),str(path)],
                         cwd=REPO,env=env,stdout=output,stderr=subprocess.STDOUT)
    check(p.returncode==0,
          f"Lean compile failed for {module}: {log.read_text(errors='replace')[-3500:]}")
    compiled.append(module)
    print(f"Compiled local source {module}",flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work",type=Path,required=True)
    ap.add_argument("--onele-run",type=int,required=True)
    args=ap.parse_args()
    work=args.work.resolve()
    work.mkdir(parents=True,exist_ok=False)
    evidence=work/"evidence";evidence.mkdir()
    linked=work/"linked";linked.mkdir()
    compiler_version=subprocess.check_output(["lean","--version"],text=True).strip()
    prefix=Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())
    compiler_sha=digest(prefix/"bin"/"lean")
    check("4.36.0-rc2" in compiler_version,"wrong Lean version")
    seen={}
    source_pins=[*PINS,dynamic_pin(args.onele_run)]
    docs={}
    for pin in source_pins:
        branch=pin[0]
        observed,manifest=gather(pin,work,compiler_sha,compiler_version)
        for name,path in observed.items():
            h=digest(path)
            if name in seen:
                check(seen[name][0]==h,
                      f"conflicting original-source object {name}: {seen[name]} != {(h,branch)}")
            else:
                dst=linked/name
                shutil.copy2(path,dst)
                seen[name]=(h,branch)
        docs[branch]={"run_id":pin[1],"artifact_id":pin[2],
                      "artifact_sha256":pin[3],
                      "source_revision":pin[4],
                      "module_count":manifest["module_count"],
                      "weighted_bound":pin[-1]}
        print(f"Authenticated {branch}: {manifest['module_count']} objects",flush=True)
    check(len(docs)==11 and len(seen)>1000,
          f"unexpected parent object union: {len(docs)} branches, {len(seen)} objects")
    index=source_index()
    busy=set();compiled=[]
    for mod in ("Raw39AcceptedSix","Raw39AcceptedSeven","Raw39AcceptedEight",
                "Raw39AcceptedNine","ExactAuditWeight",
                "Raw390LELateWeight","Raw391LELateWeight","Raw391LEBoundLift",
                "Raw39ExactJoin","Raw39CompleteJoin"):
        compile_missing(mod,linked,evidence,index,busy,compiled)
    final=evidence/"Raw39CompleteJoin.log"
    check(final.exists(),"missing final source compilation")
    subprocess.run([
        sys.executable,str(REPO/"im-results/agent4-raw109/audit_axioms.py"),
        str(final),*THEOREMS],check=True)
    check("sorryAx" not in final.read_text() and
          "native_decide" not in final.read_text(),
          "unapproved axioms in complete parent source consumer")
    receipt={"status":"source-accepted Raw39 eleven-child exact weighted Bound",
             "bound":28311,"parent_table":"1RB---_1RC---_0RD---_1LD0RA_------_------",
             "source_revision":subprocess.check_output(
                 ["git","rev-parse","HEAD"],text=True).strip(),
             "producers":docs,"unique_objects":len(seen),
             "newly_compiled":compiled,"theorems":THEOREMS,
             "root_sha256":digest(linked/"Raw39CompleteJoin.olean"),
             "lean_version":compiler_version,"lean_sha256":compiler_sha}
    (evidence/"parent-accepted.json").write_text(
        json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("PASS: exact Raw39 parent Bound 28311, source-connected all eleven children",flush=True)

if __name__=="__main__":
    main()
