"""Continue only the four missing exact cuts using the zipper proof checker.
No old accepted source or object is replaced. Export short-run partial closures."""
import json,re,sys,shutil
from pathlib import Path
from resume import merge,load,save,digest,finish
FAILED={"ZRCRecovery07Kid18Batch0081","ZRCRecovery18Kid17Batch0091","ZRCRecovery00Kid19Batch0107","ZRCRecovery12Kid17Batch0105"}
DONE={"ZRCRecovery07Kid20Batch0086","ZRCRecovery12Kid02Batch0006"}
IMP=re.compile(r"^import (\w+)$",re.M)
def prepare(w):
    core=load(w/"core.json");pool=w/"resume-pool"
    entries={e["module"]:e for e in load(w/"resume-pool.json")["modules"]}
    for d in sorted((w/"resume-cuts").iterdir()):
        if (d/"manifest.json").exists():merge(core,entries,pool,d/"manifest.json",d/"build")
    assert DONE<=entries.keys() and not (FAILED&entries.keys())
    assert set(load(w/"resume-roots.json"))==FAILED|DONE
    out=w/"imports"
    seen=set()
    def visit(n):
        if n in seen or n in entries:return
        f=out/(n+".lean")
        if not f.is_file():return
        seen.add(n)
        for dep in IMP.findall(f.read_text()):visit(dep)
    for n in sorted(FAILED):visit(n)
    changed=[]
    for n in sorted(seen):
        f=out/(n+".lean");s=f.read_text()
        if n.startswith("ZRCRecovery") and "def t" in s:
            assert n not in entries
            t=s.replace("import Hybrid\n","import OneLFZipHybrid\n").replace("BB6.Agent10FastAudit BB6.Agent6Hybrid","BB6.Agent10ZipAudit BB6.Agent6OneLFZipHybrid")
            assert t!=s,n
            f.write_text(t);changed.append(n)
    for n,e in entries.items():
        f=out/(n+".lean")
        if f.is_file():assert digest(f)==e["source_sha256"],n
    save(w/"resume-pool.json",dict(core,modules=list(entries.values()),module_count=len(entries)))
    save(w/"zip-missing.json",sorted(FAILED))
    save(w/"zip-plan.json",{"changed":changed,"reused":len(entries),"missing":sorted(FAILED)})
    print("zipper checker for",len(changed),"unaccepted declarations; preserved",len(entries),"objects",flush=True)
def last(w):
    core=load(w/"core.json");pool=w/"resume-pool"
    entries={e["module"]:e for e in load(w/"resume-pool.json")["modules"]}
    for d in sorted((w/"resume-cuts").iterdir()):
        if (d/"manifest.json").exists():merge(core,entries,pool,d/"manifest.json",d/"build")
    roots=set(load(w/"resume-roots.json"))
    missing=roots-entries.keys()
    assert missing=={"ZRCRecovery00Kid19Batch0107"},missing
    for n,e in entries.items():
        f=w/"imports"/(n+".lean")
        if f.is_file():assert digest(f)==e["source_sha256"],n
    save(w/"resume-pool.json",dict(core,modules=list(entries.values()),module_count=len(entries)))
    save(w/"zip-missing.json",sorted(missing))
    print("Continue only final root; preserved",len(entries),"source-identical objects",flush=True)
if __name__=="__main__":
    w=Path(sys.argv[2]).resolve()
    if sys.argv[1]=="prepare":prepare(w)
    elif sys.argv[1]=="last":last(w)
    elif sys.argv[1]=="finish":finish(w)
