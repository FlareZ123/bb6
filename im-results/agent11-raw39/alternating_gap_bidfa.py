"""Alternating-gap bidirectional finite-stack certificate generator.

The abstraction is a discovery device. Output is checked by FastBiDFA against
the literal original transition table, with no finite simulation assumption.
"""
from collections import defaultdict, deque
from pathlib import Path
import argparse

TABLE = "1RB0LE_1RC0RB_0RD0RA_1LD0RA_1LA0LF_1RC---".replace("_", "")

class Graph:
    def __init__(self, cap, mod, hist):
        self.cap, self.mod, self.hist = cap, mod, hist
        self.states, self.ids = [()], {(): 0}
        self.delta, self.pred = {}, defaultdict(list)
        self.push(0, 0)

    def inc(self, n):
        return n+1 if n < self.cap+self.mod-1 else self.cap

    def push(self, q, b):
        key = (q, b)
        if key in self.delta:
            return self.delta[key], False
        s = self.states[q]
        if not s:
            t = (1, 1, ()) if b else ()
        else:
            a, n, h = s
            if a == b:
                t = (b, 1, ((a,n),)+h[:self.hist-1] if self.hist else ())
            else:
                t = (b, self.inc(n), h)
        j = self.ids.get(t)
        if j is None:
            j = len(self.states)
            self.ids[t] = j
            self.states.append(t)
        self.delta[key] = j
        self.pred[j].append((b,q))
        return j, True

def solve(table, lc, rc, maxstates=1000000):
    g = [Graph(*lc), Graph(*rc)]
    p = [table[i:i+3] for i in range(0,36,3)]
    start = (0,0,0,0)
    seen, work = {start}, deque([start])
    wait = [defaultdict(set), defaultdict(set)]
    def add(st):
        if st not in seen:
            seen.add(st)
            work.append(st)
    while work:
        st = work.popleft()
        q,a,l,r = st
        mv = p[2*q+a]
        if mv == "---":
            raise ValueError("abstract path reaches undefined transition")
        w, qn = int(mv[0]), ord(mv[2])-65
        side = 0 if mv[1] == "R" else 1
        pop, t = 1-side, (l,r)
        dest,new = g[side].push(t[side],w)
        if new:
            for old in wait[side][dest]:
                work.append(old)
        wait[pop][t[pop]].add(st)
        for b,j in g[pop].pred[t[pop]]:
            add((qn,b,dest,j) if side == 0 else (qn,b,j,dest))
        if len(seen) > maxstates:
            raise ValueError("abstract-state cap")
    return g,seen

def minimize(g, states):
    old = [[0]*len(x.states) for x in g]
    while True:
        ctx = [[set() for _ in x] for x in old]
        for q,a,l,r in states:
            ctx[0][l].add((q,a,old[1][r]))
            ctx[1][r].add((q,a,old[0][l]))
        new = []
        for side in range(2):
            ids, groups = {}, []
            for i,c in enumerate(ctx[side]):
                key = (old[side][i],frozenset(c),tuple(
                    old[side][g[side].delta[i,b]] if (i,b) in g[side].delta
                    else -1 for b in (0,1)))
                groups.append(ids.setdefault(key,len(ids)))
            new.append(groups)
        if new == old:
            break
        old = new
    ds,ps = [],[]
    for side in range(2):
        size = max(old[side])+1
        d,p = [0]*(2*size),[set() for _ in range(size)]
        for (i,b),j in g[side].delta.items():
            a,c = old[side][i],old[side][j]
            d[2*a+b] = c
            p[c].add((b,a))
        ds.append(d)
        ps.append(p)
    ns = {(q,a,old[0][l],old[1][r]) for q,a,l,r in states}
    return ds,ps,ns

def verify(ds,ps,states,table):
    assert (0,0,0,0) in states
    assert all((0,0) in p[0] for p in ps)
    for q,a,l,r in states:
        mv = table[(2*q+a)*3:(2*q+a+1)*3]
        assert mv != "---"
        w,n = int(mv[0]),ord(mv[2])-65
        if mv[1] == "R":
            d = ds[0][2*l+w]
            assert (w,l) in ps[0][d]
            assert all((n,b,d,j) in states for b,j in ps[1][r])
        else:
            d = ds[1][2*r+w]
            assert (w,r) in ps[1][d]
            assert all((n,b,j,d) in states for b,j in ps[0][l])

def trie(s):
    if not s:
        return ".empty"
    if s == {0}:
        return ".leaf"
    return "(.branch "+trie({x//2 for x in s if x%2==0})+" "+trie({x//2 for x in s if x%2==1})+")"

def graph(d,p):
    return "⟨#["+ ",".join(map(str,d))+ "],#["+ ",".join(
        "["+",".join("("+str(bool(b)).lower()+","+str(j)+")" for b,j in sorted(v))+"]" for v in p)+"]⟩"

def emit(ds,ps,states,table=TABLE,ns="BB6.Agent11Raw39LE3334"):
    lines = ["import FastBiDFA","set_option maxRecDepth 100000",
             "set_option maxHeartbeats 0","namespace "+ns,
             "open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA",
             "def table : PartialMachine := fun s =>","  match s.1.val,s.2 with"]
    for i in range(12):
        mv = table[3*i:3*i+3]
        if mv != "---":
            lines.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(mv[0]=="1").lower()},{str(mv[1]=="R").lower()},{ord(mv[2])-65}⟩)')
    lines += ["  | _,_ => none",
              "def leftGraph : Graph := "+graph(ds[0],ps[0]),
              "def rightGraph : Graph := "+graph(ds[1],ps[1])]
    rows = defaultdict(set)
    for q,a,l,r in states:
        rows[2*q+a,l].add(r)
    for i in range(12):
        lines.append(f'def row{i} : Array Trie := #['+",".join(
            trie(rows[i,l]) for l in range(len(ds[0])//2))+"]")
    lines += ["def cert : BB6.Agent32FastBiDFA.Cert := ⟨leftGraph,rightGraph,#["+
              ",".join("row"+str(i) for i in range(12))+"]⟩"]
    for i in range(12):
        lines.append(f'theorem row_checked{i} : rowCheck table cert {i//2} {str(bool(i%2)).lower()} = true := by decide')
    lines += ["theorem checked : check table cert = true := by",
              "  apply check_of_rows","  · decide","  · decide","  · decide",
              "  · intro q a",
              "    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
              "    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a"]
    lines += ["    · exact row_checked"+str(i) for i in range(12)]
    lines += ["theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent32FastBiDFA.never table cert checked m hm",
              "#print axioms never","end "+ns]
    return "\n".join(lines)+"\n"

def generate(out):
    g,states = solve(TABLE,(5,8,3),(5,8,3))
    ds,ps,ns = minimize(g,states)
    verify(ds,ps,ns,TABLE)
    print("abstract",len(states),[len(x.states) for x in g],sum(len(x.delta) for x in g))
    print("quotient",len(ns),[len(d)//2 for d in ds],sum(len(s) for p in ps for s in p))
    out.write_text(emit(ds,ps,ns),encoding="utf-8")

if __name__ == "__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("output",type=Path)
    generate(ap.parse_args().output)
