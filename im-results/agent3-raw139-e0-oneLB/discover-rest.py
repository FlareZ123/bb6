"""Untrusted discovery for all still-unsearched exact C1 siblings of E0=1LB.

Keep full partitions and witnesses, so the later original-source Lean proof
does not repeat discovery. Do not call an incomplete child a Cover.
"""
import json,pathlib,sys,subprocess,concurrent.futures,time,os
from collections import defaultdict
from blockcert import generate
from package6 import first_hole

CODES=(0,1,2,3,4,5,6,7,9,13,15,19,20,21,22,23)
RECIPES=[(w,c,m,r,False,ph) for w in (2,3) for c,m,r,ph in [
 (1,1,1,False),(1,1,2,False),(1,2,1,False),(1,2,2,False),(1,3,2,False),
 (1,1,2,True),(1,1,3,True),(1,2,3,False),(2,1,2,False),(1,1,4,True),
 (1,1,3,False),(1,3,3,False),(2,2,2,False),(1,5,2,False),(1,1,5,True),
 (1,1,6,True),(1,2,4,False),(1,3,4,False),(1,5,4,False),(2,1,3,False)]]
# These additional modest width-2/3 run contexts closed five stubborn 1LC leaves.
DEEP=[(2,3,1,4,False,False),(2,3,3,5,False,False),(2,2,2,4,False,False)]
DEEP += [(w,c,m,r,False,ph) for w in (2,3) for r in (2,3,4,5,6)
         for m in (1,2,3,4,5) for c in (1,2,3) for ph in (False,True)
         if (not ph or c==1)]
DEEP=list(dict.fromkeys(DEEP))
def parent(c):return [7,24,11,24,14,c,24,16,6,11,24,24]
def write(path,obj):
    tmp=path.with_suffix(".tmp")
    tmp.write_text(json.dumps(obj,separators=(",",":"))+"\n")
    tmp.replace(path)
def trial(t,rs,lim):
    for r in rs:
        try:
            if generate(t,*r[:-1],phase=r[-1],event_limit=lim) is not None:return r
        except (AssertionError,ValueError,KeyError,IndexError):
            continue  # Candidate generation failed, not a theorem.
    return None
def search(args):
    c,replay,root=args
    work=pathlib.Path(root)/f"c{c:02d}"
    work.mkdir(parents=True,exist_ok=True)
    partfile=work/"partition.json"
    with partfile.open("w") as f:
        subprocess.run([replay,"450","2",*map(str,parent(c))],stdout=f,check=True)
    part=json.loads(partfile.read_text())
    counts=part["counts"]
    assert sum(counts[k] for k in ("cycle","last","far","open"))==1+23*counts["split"]
    assert len({tuple(t) for t in part["open"]})==counts["open"]
    assert part["tree"][0]=="split"
    groups,late,rest=defaultdict(list),{},[]
    t0=time.monotonic()
    def checkpoint(rest):
        solved=set(late)|{i for ids in groups.values() for i in ids}
        assert len(solved)==len(late)+sum(map(len,groups.values()))
        unresolved=[{"index":i,"table":t,"first":h} for i,t,h in rest]
        spec=dict(parent=parent(c),counts=counts,limit=450,maxd=2,
          bound=max([counts["maxquery"]]+[x[0] for x in late.values()])+6,
          namespace=f"BB6.Agent3E0OneLBC1Code{c:02d}",prefix=f"Raw139E0OneLBC1Code{c:02d}",
          external_imports=[],block_groups=[[p,ids] for p,ids in sorted(groups.items())],
          late=late,proven={},max_module_leaves=350,independent_root_children=True)
        write(work/"spec-compact.json",spec)
        write(work/"unresolved.json",unresolved)
        return spec
    print("PARTITION",c,counts,flush=True)
    for i,t in enumerate(part["open"]):
        h=first_hole(t,20000)
        if h[0]=="hole" and t.count(24)==1:late[i]=list(h[1:]);continue
        p=trial(t,RECIPES,50000)
        if p is not None:groups[p].append(i)
        else:rest.append((i,t,h))
        if i and i%250==0:
            print("PROGRESS",c,i,"open",len(part["open"]),"residual",len(rest),"seconds",round(time.monotonic()-t0),flush=True)
    checkpoint(rest)
    print("SHALLOW",c,"block",sum(map(len,groups.values())),"late",len(late),"residual",len(rest),flush=True)
    # Only spend the deeper search on at most 32 actual hard leaves per child.
    # Save each improved partition; leave all untouched residuals explicit.
    remain=[]
    for k,(i,t,h) in enumerate(rest):
        if t.count(24)==1 and h[0]!="hole":
            h=first_hole(t,2000000)
            if h[0]=="hole":late[i]=list(h[1:]);continue
        p=trial(t,DEEP,20000) if k<32 and time.monotonic()-t0<900 else None
        if p is not None:groups[p].append(i)
        else:remain.append((i,t,h))
    spec=checkpoint(remain)
    assert len(late)+sum(map(len,groups.values()))+len(remain)==counts["open"]
    row=dict(c=c,first=part["tree"][1:3],counts=counts,block=sum(map(len,groups.values())),
             late=len(late),bound=spec["bound"] if not remain else None,
             unresolved=len(remain),seconds=round(time.monotonic()-t0))
    print("RESULT",json.dumps(row,separators=(",",":")),flush=True)
    for i,t,h in remain[:80]:print("RESIDUAL",c,i,t,h,flush=True)
    return row
if __name__=="__main__":
    replay=str(pathlib.Path(sys.argv[1]).resolve())
    root=str(pathlib.Path(sys.argv[2]).resolve())
    codes=tuple(map(int,sys.argv[3:])) or CODES
    assert len(set(codes))==len(codes) and set(codes)<=set(CODES)
    with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
        futures=[pool.submit(search,(c,replay,root)) for c in codes]
        rows=[f.result() for f in concurrent.futures.as_completed(futures)]
    write(pathlib.Path(root)/"summary.json",sorted(rows,key=lambda x:x["c"]))
    print("SUMMARY",json.dumps(sorted(rows,key=lambda x:x["c"]),separators=(",",":")),flush=True)
