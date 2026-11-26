#!/usr/bin/env python3
import os
import re
import subprocess

EXPECTED = {
    (): (528150, 429991, 98158, 1, 0, [4]),
    (4,): (468755, 298402, 170349, 4, 12, [1]),
    (4,1): (468755, 298427, 170323, 5, 24, [2,5]),
    (4,1,2): (468761, 279719, 189038, 4, 33, [0]),
    (4,1,2,0): (468767, 279712, 189051, 4, 7, []),
    (4,1,5): (468767, 296210, 172552, 5, 18, [2]),
    (4,1,5,2): (468773, 276079, 192688, 6, 24, [2]),
    (4,1,5,2,2): (468776, 276102, 192669, 5, 22, [0]),
    (4,1,5,2,2,0): (468779, 276127, 192646, 6, 15, [3]),
    (4,1,5,2,2,0,3): (468785, 268567, 200212, 6, 36, [0]),
    (4,1,5,2,2,0,3,0): (468791, 268742, 200043, 6, 68, []),
}
seen = set()
def visit(path, c, d, L):
    assert path not in seen and path in EXPECTED
    seen.add(path)
    cut, sieve, sparse, full, extras, vs = EXPECTED[path]
    totals = [0,0,0,0]
    children = {}
    for lo, hi in [(1,25000),(25001,cut)]:
        cmd = ["./needle10","10",str(c),str(d),str(L),str(lo),str(hi)]
        out = subprocess.check_output(cmd,text=True)
        print(out,end="",flush=True)
        row = next(line for line in out.splitlines() if line.startswith("r="))
        fields = dict(re.findall(r"(\w+)=([^ ]*)",row))
        assert fields["range"] == f"{lo}..{hi}"
        assert int(fields["cut"]) == cut and int(fields["largeZero"]) == 0
        counts = [int(fields[k]) for k in ("sieve","sparse","exact","extras")]
        assert sum(counts[:3]) == hi-lo+1
        totals = [a+b for a,b in zip(totals,counts)]
        for v, cc, dd, LL in re.findall(r"(\d+)\[(-?\d+),(-?\d+),(-?\d+)\]",fields["parents"]):
            v, cc, dd, LL = map(int,(v,cc,dd,LL))
            m = v+1
            assert v not in children
            assert (cc,dd,LL) == (c*2**m,(d+L*(5-2*m))*2**m,L*(2**m+3))
            children[v] = (cc,dd,LL)
    assert totals == [sieve,sparse,full,extras]
    assert sorted(children) == vs
    for v in vs:
        visit(path+(v,),*children[v])
visit((),1,0,1)
assert seen == set(EXPECTED)
print("COMPLETE: 11 vertices, 10 edges, 2 leaves; no unresolved candidates")
