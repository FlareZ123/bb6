"""Reconstruct the exact computational witness manifest for E0=0RD.

The first successful parameter recipe is retained for each open table.
The complete recipe assignment digest pins the original local discovery.
"""
import hashlib
import json
import pathlib
import sys
from collections import Counter
from blockcert import generate

PARENT = [7,24,11,24,14,24,24,16,13,11,24,24]
COUNTS = dict(cycle=310299,last=81310,split=18648,far=32640,open=4656,maxquery=313)
PARAMS = [
    (2,1,1,1,False,False), (3,1,1,1,False,False),
    (2,1,1,2,False,True), (2,1,2,1,False,False),
    (2,1,1,2,False,False), (2,1,3,2,False,False),
    (3,1,2,2,False,False), (2,1,3,1,False,False),
    (2,1,5,2,False,False), (2,1,2,2,False,False),
    (2,1,3,4,False,False), (3,1,1,2,False,False),
    (2,1,3,3,False,True),
]
LATE = {1762: [498,1], 2113: [800,11]}
EXTRA = {475: (2,1,2,3,False,False), 447: (2,1,1,3,False,True), 1640: (2,1,5,3,False,False)}
LATE_TABLES = {
    1762: [7,24,11,23,14,8,2,16,13,11,3,17],
    2113: [7,3,11,9,14,7,22,16,13,11,2,24],
}
DIGEST = "098cc9dfb7a6035e113e585564d716c46dba43ab03d1c0c698c6acb5b7f575ea"

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
                cert = generate(table,*params[:-1],phase=params[-1],event_limit=20000 if i in EXTRA else 10000)
            except (AssertionError,KeyError,ValueError):
                continue
            if cert is not None:
                groups.setdefault(params,[]).append(i)
                assignment.append(params)
                break
        else:
            raise AssertionError(("unresolved leaf", i, table))
    ordered = sorted(groups)
    assert [len(groups[x]) for x in ordered] == [2815,492,119,1,134,40,1,315,1,25,31,1,651,28]
    labels = {p:"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"[i] for i,p in enumerate(ordered)}
    mapping = "".join("x" if x is None else labels[x] for x in assignment)
    assert hashlib.sha256(mapping.encode()).hexdigest() == DIGEST
    assert sum(map(len,groups.values())) + len(LATE) == COUNTS["open"]
    return dict(parent=PARENT,counts=COUNTS,limit=450,maxd=2,bound=806,
        namespace="BB6.Agent48Raw139E0ZeroRD",prefix="Raw139E0ZeroRD",
        external_imports=[],block_groups=[[p,groups[p]] for p in ordered],
        late=LATE,proven={},max_module_leaves=1800)

if __name__ == "__main__":
    partition = json.loads(pathlib.Path(sys.argv[1]).read_text())
    spec = discover(partition)
    pathlib.Path(sys.argv[2]).write_text(json.dumps(spec,separators=(",",":"))+"\n")
    print("recovered all 4656 open-leaf recipes; assignment digest",DIGEST)
