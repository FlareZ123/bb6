"""Reconstruct the exact computational witness manifest for E0=1RB.

The first successful parameter recipe is retained for each open table.
The complete recipe assignment digest pins the original local discovery.
"""
import hashlib
import json
import pathlib
import sys
from collections import Counter
from blockcert import generate

PARENT = [7,24,11,24,14,24,24,16,7,11,24,24]
COUNTS = dict(cycle=288501,last=64523,split=16948,far=33424,open=3357,maxquery=430)
PARAMS = [
    (2,1,1,1,False,False), (3,1,1,1,False,False),
    (2,1,1,2,False,True), (2,1,2,1,False,False),
    (2,1,1,2,False,False), (2,1,3,2,False,False),
    (3,1,2,2,False,False), (2,1,3,1,False,False),
    (2,1,5,2,False,False), (2,1,2,2,False,False),
    (2,1,3,4,False,False), (3,1,1,2,False,False),
    (2,1,3,3,False,True),
]
LATE = {428:[974,6],459:[974,6],613:[103013,6],1401:[754,6],2292:[878,6],2321:[551,6],2332:[551,6],2347:[2434,10],2924:[486,6],2925:[486,6]}
EXTRA = {i: tuple(p) for p, ids in [[[2,1,2,3,False,False],[111,112,159,160,427,458,2757,2776,2779,2789,2851,2852,2884,2885,3315,3316]],[[3,2,4,4,False,False],[226]],[[2,1,5,4,False,True],[329,338]],[[2,1,2,2,False,True],[413]],[[2,1,2,4,False,False],[429,460]],[[3,1,1,3,False,True],[430,433,461,464,3158]],[[3,1,2,3,False,True],[722]],[[3,1,5,4,False,False],[982]],[[3,1,1,4,False,True],[1384,1385,1386,1387,2062]],[[2,1,1,3,False,False],[1405]],[[2,1,2,5,False,False],[1455,1461]],[[2,2,1,4,False,False],[2027]],[[2,1,2,3,False,True],[2540,2551]],[[2,1,2,1,False,True],[2595,2982]],[[3,1,1,6,False,True],[2688]]] for i in ids}
LATE_TABLES = {428:[7,1,11,1,14,20,24,16,7,11,3,10],459:[7,1,11,1,14,20,24,16,7,11,19,10],613:[7,20,11,0,14,1,24,16,7,11,6,12],1401:[7,8,11,23,14,2,24,16,7,11,5,21],2292:[7,20,11,1,14,3,24,16,7,11,14,2],2321:[7,5,11,21,14,3,24,16,7,11,10,2],2332:[7,5,11,21,14,3,24,16,7,11,10,18],2347:[7,9,11,1,14,3,20,16,7,11,24,12],2924:[7,9,11,3,14,23,24,16,7,11,1,4],2925:[7,9,11,3,14,23,24,16,7,11,17,4]}
DIGEST = "413ed105729e8ed0445159c5e734632f9cf0cc3c1f8619b074bb74ffd9828745"

def discover(partition):
    assert partition["counts"] == COUNTS
    groups = {}
    assignment = []
    for i,table in enumerate(partition["open"]):
        if i in LATE:
            assert table == LATE_TABLES[i]
            assignment.append(None)
            continue
        for params in ([EXTRA[i]] if i in EXTRA else PARAMS):
            try:
                cert = generate(table,*params[:-1],phase=params[-1],event_limit=50000 if i in EXTRA else 10000)
            except (AssertionError,KeyError,ValueError):
                continue
            if cert is not None:
                groups.setdefault(params,[]).append(i)
                assignment.append(params)
                break
        else:
            raise AssertionError(("unresolved leaf", i, table))
    ordered = sorted(groups)
    assert [len(groups[x]) for x in ordered] == [1015,753,140,1,1,2,244,1,16,2,2,2,397,7,215,134,2,1,323,5,5,1,75,1,1,1]
    labels = {p:"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"[i] for i,p in enumerate(ordered)}
    mapping = "".join("x" if x is None else labels[x] for x in assignment)
    assert hashlib.sha256(mapping.encode()).hexdigest() == DIGEST
    assert sum(map(len,groups.values())) + len(LATE) == COUNTS["open"]
    return dict(parent=PARENT,counts=COUNTS,limit=450,maxd=2,bound=103019,
        namespace="BB6.Agent48Raw139E0OneRB",prefix="Raw139E0OneRB",
        external_imports=[],block_groups=[[p,groups[p]] for p in ordered],
        late=LATE,proven={},max_module_leaves=1800)

if __name__ == "__main__":
    partition = json.loads(pathlib.Path(sys.argv[1]).read_text())
    spec = discover(partition)
    pathlib.Path(sys.argv[2]).write_text(json.dumps(spec,separators=(",",":"))+"\n")
    print("recovered all 3357 open-leaf recipes; assignment digest",DIGEST)
