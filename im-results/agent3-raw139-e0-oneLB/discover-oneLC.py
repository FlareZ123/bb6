"""Close the exact C1=1LC sibling using the witnessed block recipe search."""
import json,pathlib,sys
from collections import defaultdict
from blockcert import generate
from package6 import first_hole
part=json.loads(pathlib.Path(sys.argv[1]).read_text())
expected=dict(cycle=11340,last=3209,split=685,far=969,open=238,maxquery=362)
assert part["counts"]==expected,part["counts"]
assert part["tree"][:3]==["split",12,6],part["tree"][:3]
assert len({tuple(t) for t in part["open"]})==238
recipes=[(w,c,m,r,False,ph) for w in (2,3) for c,m,r,ph in [
 (1,1,1,False),(1,1,2,False),(1,2,1,False),(1,2,2,False),(1,3,2,False),
 (1,1,2,True),(1,1,3,True),(1,2,3,False),(2,1,2,False),(1,1,4,True),
 (1,1,3,False),(1,3,3,False),(2,2,2,False),(1,5,2,False),(1,1,5,True),
 (1,1,6,True),(1,2,4,False),(1,3,4,False),(1,5,4,False),(2,1,3,False)]]
overrides={
 (7,23,11,5,14,10,21,16,6,11,24,3):(2,3,1,4,False,False),
 (7,20,11,5,14,10,2,16,6,11,11,24):(2,3,3,5,False,False),
 (7,22,11,5,14,10,2,16,6,11,8,24):(2,2,2,4,False,False),
 (7,22,11,5,14,10,2,16,6,11,16,24):(2,3,3,5,False,False),
 (7,22,11,5,14,10,2,16,6,11,15,24):(2,3,3,5,False,False)}
long=(7,3,11,21,14,10,1,16,6,11,24,13)
groups,late=defaultdict(list),{}
for i,t in enumerate(part["open"]):
    h=first_hole(t,61179 if tuple(t)==long else 20000)
    if h[0]=="hole" and t.count(24)==1:
        late[i]=list(h[1:])
        if tuple(t)==long: assert h==("hole",61179,10)
        continue
    candidates=[overrides[tuple(t)]] if tuple(t) in overrides else recipes
    for p in candidates:
        if generate(t,*p[:-1],phase=p[-1],event_limit=50000) is not None:
            groups[p].append(i)
            break
    else: raise AssertionError(("unclosed",i,t))
assert len(late)==5 and sum(map(len,groups.values()))==233
assert max(v[0] for v in late.values())==61179
spec=dict(parent=[7,24,11,24,14,10,24,16,6,11,24,24],counts=expected,
 limit=450,maxd=2,bound=61185,namespace="BB6.Agent3E0OneLBC1OneLC",prefix="Raw139E0OneLBC1OneLC",
 external_imports=[],block_groups=[[p,ids] for p,ids in sorted(groups.items())],late=late,
 proven={},max_module_leaves=350,independent_root_children=True)
pathlib.Path(sys.argv[2]).write_text(json.dumps(spec,separators=(",",":"))+"\n")
print("complete exact partition:",expected,"233 block invariants, final-hole witnesses",late,flush=True)
