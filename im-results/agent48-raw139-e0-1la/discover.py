"""Reproduce candidate certificates for the new E0=1LA parent.
An open leaf remains an explicit obligation; no incomplete proof is packaged.
"""
import json
import pathlib
import sys
from itertools import product
from blockcert import generate
from package6 import first_hole

PARENT=[7,24,11,24,14,24,24,16,2,11,24,24]
INITIAL=[
    (2,1,1,1,False,False),(3,1,1,1,False,False),
    (2,1,1,2,False,True),(2,1,2,1,False,False),
    (2,1,1,2,False,False),(2,1,3,2,False,False),
    (3,1,2,2,False,False),(2,1,3,1,False,False),
    (2,1,5,2,False,False),(2,1,2,2,False,False),
    (2,1,3,4,False,False),(3,1,1,2,False,False),
    (2,1,3,3,False,True)]
EXTRA=[(w,c,m,n,False,ph)
       for w,c,m,n,ph in product((2,3,4),(1,2),(1,2,3,5,7),(1,2,3,4),(False,True))
       if (w,c,m,n,False,ph) not in INITIAL]
def discover(partition):
    groups,late,remaining={}, {}, []
    counts=partition["counts"]
    for i,table in enumerate(partition["open"]):
        for params in INITIAL:
            try:
                cert=generate(table,*params[:-1],phase=params[-1],event_limit=10000)
            except (AssertionError,KeyError,ValueError):
                continue
            if cert is not None:
                groups.setdefault(params,[]).append(i)
                break
        else:
            remaining.append((i,table))
    print("Initial unresolved",len(remaining),flush=True)
    unresolved=[]
    for i,table in remaining:
        replay=first_hole(table,2_000_000)
        if replay[0]=="hole" and table.count(24)==1:
            late[i]=list(replay[1:])
            print("late",i,late[i],flush=True)
            continue
        for params in EXTRA:
            try:
                cert=generate(table,*params[:-1],phase=params[-1],event_limit=30000)
            except (AssertionError,KeyError,ValueError):
                continue
            if cert is not None:
                groups.setdefault(params,[]).append(i)
                break
        else:
            unresolved.append((i,table,replay))
            print("UNRESOLVED",i,table,replay,flush=True)
    spec=dict(parent=PARENT,counts=counts,limit=450,maxd=2,
              bound=max([counts["maxquery"]]+[v[0] for v in late.values()])+6,
              namespace="BB6.Agent48Raw139E0OneLA",prefix="Raw139E0OneLA",
              external_imports=[],block_groups=[[p,groups[p]] for p in sorted(groups)],
              late=late,proven={},max_module_leaves=1800)
    assert sum(map(len,groups.values()))+len(late)+len(unresolved)==counts["open"]
    return spec,unresolved

if __name__=="__main__":
    partition=json.loads(pathlib.Path(sys.argv[1]).read_text())
    spec,unresolved=discover(partition)
    pathlib.Path(sys.argv[2]).write_text(json.dumps(spec,separators=(",",":"))+"\n")
    pathlib.Path(sys.argv[3]).write_text(json.dumps(unresolved)+"\n")
    print("counts",partition["counts"],"bound",spec["bound"],"unresolved",len(unresolved),flush=True)
    if unresolved:
        sys.exit(3)
