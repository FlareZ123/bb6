"""Reconstruct the exact computational witness manifest for E0=0RB.

The first successful parameter recipe is retained for each open table.
The complete recipe assignment digest pins the original local discovery.
"""
import hashlib
import json
import pathlib
import sys
from collections import Counter
from blockcert import generate

PARENT = [7,24,11,24,14,24,24,16,5,11,24,24]
COUNTS = dict(cycle=330158,last=70001,split=18483,far=22834,open=2117,maxquery=367)
PARAMS = [
    (2,1,1,1,False,False), (3,1,1,1,False,False),
    (2,1,1,2,False,True), (2,1,2,1,False,False),
    (2,1,1,2,False,False), (2,1,3,2,False,False),
    (3,1,2,2,False,False), (2,1,3,1,False,False),
    (2,1,5,2,False,False), (2,1,2,2,False,False),
    (2,1,3,4,False,False), (3,1,1,2,False,False),
    (2,1,3,3,False,True),
]
LATE = {440: [1211,6], 2093: [1121,3]}
LATE_TABLES = {
    440: [7,20,11,3,14,1,24,16,5,11,2,8],
    2093: [7,0,11,24,14,23,2,16,5,11,9,19],
}
DIGEST = "9c70d72dee996472c992048c9d74903626a6fb00c15453cf1b78e29677212839"

def discover(partition):
    assert partition["counts"] == COUNTS
    groups = {}
    assignment = []
    for i,table in enumerate(partition["open"]):
        if i in LATE:
            assert table == LATE_TABLES[i]
            assignment.append(None)
            continue
        for params in PARAMS:
            try:
                cert = generate(table,*params[:-1],phase=params[-1],event_limit=10000)
            except (AssertionError,KeyError,ValueError):
                continue
            if cert is not None:
                groups.setdefault(params,[]).append(i)
                assignment.append(params)
                break
        else:
            raise AssertionError(("unresolved leaf", i, table))
    ordered = sorted(groups)
    assert [len(groups[x]) for x in ordered] == [1516,65,69,40,10,38,2,12,6,352,5]
    labels = {p:"0123456789A"[i] for i,p in enumerate(ordered)}
    mapping = "".join("x" if x is None else labels[x] for x in assignment)
    assert hashlib.sha256(mapping.encode()).hexdigest() == DIGEST
    assert sum(map(len,groups.values())) + len(LATE) == COUNTS["open"]
    return dict(parent=PARENT,counts=COUNTS,limit=450,maxd=2,bound=1217,
        namespace="BB6.Agent48Raw139E0ZeroRB",prefix="Raw139E0ZeroRB",
        external_imports=[],block_groups=[[p,groups[p]] for p in ordered],
        late=LATE,proven={},max_module_leaves=1800)

if __name__ == "__main__":
    partition = json.loads(pathlib.Path(sys.argv[1]).read_text())
    spec = discover(partition)
    pathlib.Path(sys.argv[2]).write_text(json.dumps(spec,separators=(",",":"))+"\n")
    print("recovered all 2117 open-leaf recipes; assignment digest",DIGEST)
