#!/usr/bin/env python3
"""Finite run-aware stack abstraction for the exact Raw118 residual roster.

Each stack summary reads bits from the distant end towards the head. It stores
the last k runs of raw bits or lagged XOR differences, with each length
represented exactly below c and modulo p thereafter. The last lag raw bits are retained for XOR updates; optional blank
padding normalization maps an initial zero push to the empty state. Empty stack is a separate state and has its own
implicit blank-pop edge. Only observed push transitions are needed; remaining
DFA entries are filled with zero and the independent BiDFA replay must pass.

Discovery is untrusted: source checking uses the existing IndexedBiDFA theorem.
"""
from collections import defaultdict, deque
from pathlib import Path
import hashlib
import json
import sys
import tempfile

HERE = Path(__file__).resolve().parent
A1 = HERE.parent / "agent1-bidfa-sat"
A16 = HERE.parent / "agent16-raw118"
sys.path[:0] = [str(A1), str(A16)]
from bidfa_emit import witness
from wide_cert import emit

ROSTER_SHA = "0fd10d3adcc48fba9badb4357ad3b19453f5215ce35fdb57f38034ebc3933c0c"
# (left parameters, right parameters), (k, c, p, XOR lag[, trim]).
# Lag zero means raw bits; positive lag compares with the earlier raw bit.
HITS = {
    430: ((3,4,6,0,1),(3,4,6,0,1)),
    437: ((4,3,8,2,1),(4,3,8,2,1)),
    440: ((3,4,6,0,1),(3,4,6,0,1)),
    456: ((4,4,6,0,1),(4,4,6,0,1)),
    1181: ((5,6,5,0,1),(5,6,5,1,1)),
    3908: ((4,2,2,0,1),(4,2,2,4,1)),
    1120: ((3,3,4,0),(3,3,4,1)),
    1127: ((3,2,4,1),(3,2,4,1)),
    1174: ((3,3,4,0),(3,3,4,1)),
    1326: ((3,3,4,0),(3,3,4,1)),
    1390: ((4,2,3,1),(4,2,3,0)),
    1391: ((4,2,3,1),(4,2,3,0)),
    1392: ((4,4,3,1),(4,4,3,0)),
    1816: ((3,3,4,0),(3,3,4,1)),
    2867: ((3,3,3,0),(3,3,3,1)),
    3921: ((4,4,4,0),(4,4,4,0)),
    4093: ((3,2,3,1),(3,2,3,1)),
    4125: ((4,3,4,1),(4,3,4,0)),
    4342: ((2,3,4,1),(2,3,4,0)),
    4443: ((3,3,4,0),(3,3,4,1)),
}

class Side:
    def __init__(self, params):
        self.k,self.c,self.p,self.mode = params[:4]
        self.trim = bool(params[4]) if len(params) == 5 else False
        assert self.k >= 1 and self.c >= 1 and self.p >= 1
        self.keys = [0]
        self.ids = {0:0}
        self.delta = [[-1,-1]]
        self.edges = [set([(0,0)])]
        self.wait = [[]]

    def push(self, i, b):
        dest = self.delta[i][b]
        if dest >= 0:
            return dest
        v = self.keys[i]
        if self.trim and v == 0 and b == 0:
            self.delta[i][b] = 0
            return 0
        h = max(1,self.mode)
        mask = (1 << h)-1
        hist = v & mask
        prev = (v >> h) & 1
        digits = v >> (h+1)
        bit = b ^ ((hist >> (h-1)) & 1) if self.mode else b
        count = digits & 31
        if not count or bit != prev:
            digits = ((digits << 5) | 1) & ((1 << (5*self.k))-1)
        else:
            n = count+1
            if n >= self.c+self.p:
                n = self.c
            digits = (digits & ~31) | n
        key = (digits << (h+1)) | (bit << h) | (((hist << 1) | b) & mask)
        dest = self.ids.get(key)
        if dest is None:
            dest = len(self.keys)
            self.keys.append(key)
            self.ids[key] = dest
            self.delta.append([-1,-1])
            self.edges.append(set())
            self.wait.append([])
        self.delta[i][b] = dest
        return dest

def discover(table, lp, rp, cap=100000):
    sides = [Side(lp), Side(rp)]
    raw = table.replace("_","")
    moves = [raw[i:i+3] for i in range(0,36,3)]
    seen = {(0,0,0,0)}
    todo = deque(seen)
    def add(q,b,l,r):
        if moves[2*q+b] == "---":
            raise ValueError("abstract hole reached")
        s = (q,b,l,r)
        if s not in seen:
            if len(seen) >= cap:
                raise ValueError("abstract state cap")
            seen.add(s)
            todo.append(s)
    def pop(s,e):
        q,b,l,r = s
        w,dr,n = moves[2*q+b]
        w,n = int(w),ord(n)-65
        sym,src = e
        if dr == "R":
            add(n,sym,sides[0].delta[l][w],src)
        else:
            add(n,sym,src,sides[1].delta[r][w])
    while todo:
        s = todo.popleft()
        q,b,l,r = s
        move = moves[2*q+b]
        if move == "---":
            raise ValueError("abstract hole reached")
        w,dr,n = move
        w = int(w)
        ps = 0 if dr == "R" else 1
        ts = 1-ps
        old,x = (l,r) if ps == 0 else (r,l)
        push = sides[ps]
        dest = push.push(old,w)
        e = (w,old)
        if e not in push.edges[dest]:
            push.edges[dest].add(e)
            for st in push.wait[dest]:
                pop(st,e)
        sides[ts].wait[x].append(s)
        for e in sorted(sides[ts].edges[x]):
            pop(s,e)
    d = [[max(0,x) for pair in s.delta for x in pair] for s in sides]
    edges, states = witness(table,*d)
    assert set(states) == seen
    return d, len(states), sum(map(len,edges))

def main(indices):
    roster = (A1 / "raw118-hard87.tsv").read_bytes()
    assert hashlib.sha256(roster).hexdigest() == ROSTER_SHA
    tables = {int(i):t for i,t in (x.split() for x in roster.decode().splitlines())}
    assert len(tables) == 87 and all(t.count("---")==1 for t in tables.values())
    sat = {int(x["index"]) for x in json.loads((A1/"raw118-sat-hits.json").read_text())}
    wide = {int(i) for i in json.loads((A1/"raw118-wide-widths.json").read_text())}
    assert not (set(HITS) & (sat | wide | {3970}))
    output = HERE / "run-generated"
    output.mkdir(exist_ok=True)
    found = []
    for i in indices:
        t = tables[i]
        lp,rp = HITS[i]
        d,n,e = discover(t,lp,rp)
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            n2,e2 = emit(i,t,*d,temp)
            assert (n,e)==(n2,e2)
            for f in sorted(temp.glob("*.lean")):
                body = f.read_text().replace(f"Raw118Wide{i}",f"Raw118Run{i}").replace("BB6Coverage.Agent1BiDFAWide", "BB6Coverage.Agent40Raw118Run")
                (output / f.name.replace(f"Raw118Wide{i}",f"Raw118Run{i}")).write_text(body)
        row = {"index":i,"table":t,"left_params":lp,"right_params":rp,
               "left":d[0],"right":d[1],"states":n,"edges":e}
        found.append(row)
        print("RUN SUMMARY",i,lp,rp,"states",n,"edges",e,flush=True)
    (output/"manifest.json").write_text(json.dumps(found,indent=2)+"\n")
    print("Generated",len(found),"candidate leaves",flush=True)

if __name__ == "__main__":
    main([int(x) for x in sys.argv[1:]] or sorted(HITS))
