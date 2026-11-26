#!/usr/bin/env python3
"""Shard the existing RC certificates; no new candidate search."""
import hashlib, json, os, re, shutil, subprocess, sys, zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
SRC=Path(__file__).resolve().parent
WORK=Path(os.environ.get("RC_WORK","/tmp/rc-audit")).resolve()
CORE=WORK/"core"
OUT=Path(os.environ.get("RC_OUT","/tmp/rc-out")).resolve()
TABLE="1RB---_1RC---_0RD---_1LD1RE_---1LF_1RC0LF"
CORE_SHA="2231c274970b233002894c3fa097e3b81ad1484a3db0809c0148f8c03e26c477"
CORE_RUN=45762057732
CORE_ARTIFACT=15090715339
ALLOWED={"propext","Classical.choice","Quot.sound"}
def digest(p):
    with p.open("rb") as f:
        return hashlib.file_digest(f,"sha256").hexdigest()
def run(*args,cwd=WORK,**kw):
    subprocess.run([str(a) for a in args],cwd=cwd,check=True,**kw)
def compile_module(mod):
    env=dict(os.environ,LEAN_PATH=str(CORE))
    log=CORE/(mod+".log")
    with log.open("w") as f:
        run("lean","-j","1","-o",mod+".olean",mod+".lean",cwd=CORE,env=env,stdout=f,stderr=subprocess.STDOUT)
    text=log.read_text()
    assert "sorryAx" not in text and "native_decide" not in text,mod
    for ax in re.findall(r"depends on axioms: \[([^\]]*)\]",text):
        assert set(x.strip() for x in ax.split(",") if x.strip())<=ALLOWED,(mod,ax)
    print(mod,flush=True)
def reachable(roots):
    lib=Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())/"lib/lean"
    walk=ROOT/"im-results/agent31-shared-core/WalkImportClosure.lean"
    out=subprocess.check_output(["lean","--run",str(walk),str(lib),"1",str(CORE),*roots],text=True)
    return [Path(s) for s in out.splitlines() if s]
def split_group(mod):
    p=CORE/(mod+".lean"); s=p.read_text()
    a=s.index("def table"); b=s.index("theorem row_"); c=s.index("theorem left_nonempty")
    head=s[:a]; end=s[s.rindex("\nend "):]
    base=mod+"Base"
    (CORE/(base+".lean")).write_text(s[:b]+end)
    order=[base]; body=s[b:c]
    starts=list(re.finditer(r"(?m)^theorem row_(\d+)_",body))
    for j in range(12):
        hits=[m for m in starts if int(m.group(1))==j]
        assert hits
        start=hits[0].start(); stop=next((m.start() for m in starts if m.start()>start and int(m.group(1))!=j),len(body))
        name=mod+f"Row{j:02}"
        (CORE/(name+".lean")).write_text(f"import {base}\n"+head+body[start:stop]+end)
        order.append(name)
    p.write_text("".join(f"import {m}\n" for m in order[1:])+head+s[c:])
    return order+[mod]
def balance(tasks,n):
    bins=[[] for _ in range(n)]; weights=[0]*n
    for task in sorted(tasks,key=lambda t:-sum((CORE/(m+".lean")).stat().st_size for m in t)):
        j=min(range(n),key=weights.__getitem__)
        bins[j].extend(task); weights[j]+=sum((CORE/(m+".lean")).stat().st_size for m in task)
    return bins
def prepare():
    WORK.mkdir(parents=True,exist_ok=True)
    info=json.loads(subprocess.check_output(["gh","api",f"repos/FlareZ123/bb6/actions/runs/{CORE_RUN}"]))
    assert info["conclusion"]=="success"
    archive=WORK/"accepted.zip"
    with archive.open("wb") as f:
        run("gh","api",f"repos/FlareZ123/bb6/actions/artifacts/{CORE_ARTIFACT}/zip",stdout=f)
    assert digest(archive)==CORE_SHA
    CORE.mkdir(exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        manifest=json.loads(z.read("manifest.json"))
        binary=Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())/"bin/lean"
        assert digest(binary)==manifest["lean_binary"]["sha256"]
        for m in manifest["modules"]:
            rel=m["olean_path"]; assert Path(rel).name==rel
            p=CORE/rel; p.write_bytes(z.read(rel))
            assert digest(p)==m["olean_sha256"]
    archive.unlink()
    run(sys.executable,SRC/"unpack.py",WORK)
    shutil.copyfile(ROOT/"im-results/agent2-tnf-raw124/Raw124FastAudit.lean",CORE/"Raw124FastAudit.lean")
    run("c++","-O2","-std=c++20","partition.cpp","-o","partition")
    run("./partition",TABLE,"3000","32","rc")
    assert digest(WORK/"rc.json")=="8eafc439ae0076103fef4d0946346d8aa94fcc2226c358bd3250e3bd761ba15d"
    assert digest(WORK/"rc.open")=="e70042677f994e37339e7d1ad707ac3b3bd4172aad2c89fa15364bcc5f8aed9e"
    run(sys.executable,"gen_auto.py")
    run(sys.executable,"gen_mask.py")
    run(sys.executable,SRC/"generate_late_verified.py")
    run(sys.executable,"gen_audit.py")
    common=["Raw124FastAudit","Agent12RCBase","MaskTwoSided","PackedRC","LateRCBridge","RichRCAudit","SevenRC"]
    for m in common:compile_module(m)
    keep=set(reachable(common+["TwoSidedAutomata"]))
    for p in CORE.glob("*.olean"):
        if p not in keep:p.unlink()
    tasks=[[p.stem] for p in sorted(CORE.glob("Agent12RCM*.lean"))]
    tasks.extend(split_group(mod) for _,_,mod in json.loads((WORK/"maskgroups.json").read_text()))
    tasks.extend(p.read_text().splitlines() for p in sorted(WORK.glob("late*.order")))
    audit=(WORK/"audit.order").read_text().splitlines()
    groups={}
    for m in audit:
        match=re.match(r"Agent12RCKidRoot_(\d\d)",m)
        if match:groups.setdefault(match.group(1),[]).append(m)
    assert len(groups)==24
    plan={"witness":balance(tasks,20),"audit":balance(list(groups.values()),12),
          "common":{p.name:digest(p) for p in CORE.glob("*.olean")},
          "sources":{p.name:digest(p) for p in CORE.glob("*.lean")}}
    (WORK/"plan.json").write_text(json.dumps(plan,sort_keys=True,indent=2))
    OUT.mkdir(parents=True,exist_ok=True)
    shutil.copytree(CORE,OUT/"core",dirs_exist_ok=True,ignore=shutil.ignore_patterns("*.log"))
    shutil.copyfile(WORK/"plan.json",OUT/"plan.json")
def merge(kind,plan):
    directory=Path("/tmp/rc-"+kind)
    for i,mods in enumerate(plan[kind]):
        folder=directory/f"raw124-rc-{kind}-{i}"
        manifest=json.loads((folder/"manifest.json").read_text())
        assert set(manifest)==set(mods)
        for m in mods:
            p=folder/(m+".olean")
            assert digest(p)==manifest[m]
            assert not (CORE/p.name).exists()
            shutil.copyfile(p,CORE/p.name)
def shard(kind,i):
    plan=json.loads((WORK/"plan.json").read_text())
    for name,sha in plan["sources"].items():assert digest(CORE/name)==sha,name
    for name,sha in plan["common"].items():assert digest(CORE/name)==sha,name
    if kind in ("audit","final"):merge("witness",plan)
    if kind=="final":
        merge("audit",plan)
        mods=["Agent12RCKidRoot","Agent12RCFinal"]
    else:mods=plan[kind][i]
    OUT.mkdir(parents=True,exist_ok=True)
    for m in mods:compile_module(m)
    if kind!="final":
        for m in mods:shutil.copyfile(CORE/(m+".olean"),OUT/(m+".olean"))
        (OUT/"manifest.json").write_text(json.dumps({m:digest(CORE/(m+".olean")) for m in mods}))
    else:
        log=(CORE/"Agent12RCFinal.log").read_text()
        assert "BB6.Agent12Raw124ZeroLF1RC.bound_all" in log,log
        print(log)
        objects=reachable(["Agent12RCFinal"])
        for p in objects:shutil.copyfile(p,OUT/p.name)
        manifest={"claim":{"theorem":"BB6.Agent12Raw124ZeroLF1RC.bound_all","parent_table":TABLE,"weighted_bound":108667},
          "core_artifact":CORE_ARTIFACT,"core_sha256":CORE_SHA,
          "proof_source_revision":os.environ.get("GITHUB_SHA","local"),
          "objects":{p.name:digest(p) for p in objects},"source_sha256":plan["sources"],
          "lean_version":subprocess.check_output(["lean","--version"],text=True).strip(),"axiom_log":log}
        (OUT/"manifest.json").write_text(json.dumps(manifest,sort_keys=True,indent=2))
        shutil.copyfile(CORE/"Agent12RCFinal.log",OUT/"lean.log")
if __name__=="__main__":
    mode=sys.argv[1]
    if mode=="prepare":prepare()
    else:shard(mode,int(sys.argv[2]) if len(sys.argv)>2 else 0)
