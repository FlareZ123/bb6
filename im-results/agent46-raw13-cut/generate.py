#!/usr/bin/env python3
"""Generate the canonical raw13 partial audit. Only Lean checker acceptance
can certify the output. No time limit is used as evidence of nonhalting."""
from collections import Counter
from itertools import product
from pathlib import Path

D = Path(__file__).resolve().parent
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
DECODE = {v:(int(v[0]),1 if v[1]=="R" else -1,ord(v[2])-65) for v in MOVES}
ROOT = ["1RB",None,"1RC",None,"1LA",None,None,None,None,None,None,None]
TARGET = "1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE".replace("_","")
TARGET = [TARGET[i:i+3] for i in range(0,36,3)]
DEPTH = 3
LIMIT = 100

def mask(p):
    reached, todo = {0}, [0]
    while todo:
        s = todo.pop()
        for b in range(2):
            v = p[2*s+b]
            if v not in DECODE:
                return None
            q = DECODE[v][2]
            if q not in reached:
                reached.add(q)
                todo.append(q)
    return sum(1<<s for s in reached)

def scan(p):
    st,h,ones = 0,0,frozenset()
    hist = []
    for n in range(LIMIT+1):
        lo = hi = h
        for e in range(n-1,-1,-1):
            q,j,c = hist[e]
            lo,hi = min(lo,j),max(hi,j)
            if q != st:
                continue
            delta = h-j
            if delta >= 0 and {x+delta for x in c if x>=lo} == {x for x in ones if x>=lo+delta}:
                return ("cycle",e,n-e,True,lo)
            if delta <= 0 and {x+delta for x in c if x<=hi} == {x for x in ones if x<=hi+delta}:
                return ("cycle",e,n-e,False,hi)
        s = 2*st+(h in ones)
        v = p[s]
        if v is None:
            return ("hole",n,s)
        if n == LIMIT:
            return ("timeout",)
        hist.append((st,h,ones))
        w,d,st = DECODE[v]
        ones = ones|{h} if w else ones-{h}
        h += d

def tree(p,cut,depth,auth=False):
    m = mask(p)
    if m:
        return ("state",m)
    r = scan(p)
    if r[0] == "cycle":
        return r
    if r[0] != "hole":
        return ("open",)
    _,n,s = r
    if p.count(None) == 1:
        return ("last",n,s)
    if depth <= 0 and not auth:
        return ("open",)
    kids = []
    for mv in MOVES:
        q = DECODE[mv][2]
        if q > cut:
            kids.append(None)
            continue
        c = p[:]
        c[s] = mv
        kids.append(tree(c,max(cut,q+1),depth-1,auth and mv==TARGET[s]))
    return ("split",n,s,kids)

def tally(t,holes,cut,c,m,weight=1):
    tag = t[0]
    c[tag] += 1
    if tag == "split":
        c["halt"] += 1
        m["halt"] += weight*25**(holes-1)
        for mv,k in zip(MOVES,t[3]):
            if k is None:
                continue
            q = DECODE[mv][2]
            tally(k,holes-1,max(cut,q+1),c,m,weight*((6-cut) if q==cut else 1))
    else:
        m[tag] += weight*25**holes

def boolean(b):
    return str(bool(b)).lower()

def move(mv):
    w,d,q = DECODE[mv]
    return f"⟨{boolean(w)},{boolean(d==1)},{q}⟩"

def slot(s):
    return f"({s//2},{boolean(s%2)})"

def emit(t):
    if t is None or t[0] == "open":
        return ".unresolved"
    tag,*v = t
    if tag == "state":
        return f".state {v[0]}"
    if tag == "cycle":
        e,k,r,b = v
        return f".closed (.cycle {e} {k} {boolean(r)} ({b}))"
    if tag == "last":
        n,s = v
        return f".closed (.last {n} {slot(s)})"
    assert tag == "split"
    n,s,kids = v
    return f".split {n} {slot(s)} (byCutMove [\n"+",\n".join(map(emit,kids))+"])"

HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
"""

def write(name,imports,body):
    (D/(name+".lean")).write_text("".join(f"import {i}\n" for i in imports)+HEADER+body+"\nend BB6.Agent46Raw13\n",encoding="utf-8")

if __name__ == "__main__":
    t = tree(ROOT,3,DEPTH,True)
    assert t[:3] == ("split",3,1)
    c,m = Counter(),Counter()
    tally(t,9,3,c,m)
    assert c == Counter(open=1760,cycle=696,state=688,split=176,halt=176,last=13),c
    assert m["open"] == 1733719053700 and sum(m.values()) == 25**9,m
    names = []
    for i,k in enumerate(t[3]):
        if k is None:
            continue
        name = f"Agent46Raw13Kid{i:02}"
        names.append(name)
        mv = move(MOVES[i])
        write(name,["Agent46Raw13Base"],f"""
def kid{i:02} : Cut := {emit(k)}
theorem checked{i:02} :
    check 7014 (child {mv}) (nextCut 3 {mv}) kid{i:02} = true := by decide
""")
    terms = ",".join(f"kid{i:02}" if k is not None else ".unresolved" for i,k in enumerate(t[3]))
    cases = "\n".join(f"  · exact checked{12*w+6*r+q:02}" for q,w,r in product(range(4),range(2),range(2)))
    write("Agent46Raw13Data",names,f"""
def kids : Move → Cut := byCutMove [{terms}]
theorem kids_checked (mv : Move) (hv : mv.next.val ≤ 3) :
    check 7014 (child mv) (nextCut 3 mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hq with rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}

def raw13Cut : Cut := .split 3 (0,true) kids

theorem cut_checked : check 7014 raw13 3 raw13Cut = true := by
  change (BB6.Agent10ZipAudit.zipQueryOK 7014 raw13 3 (0,true) &&
    BB6.Agent31ThreeHole.allMoves (fun mv =>
      if mv.next.val ≤ 3 then check 7014 (child mv) (nextCut 3 mv) (kids mv)
      else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, BB6.Agent31ThreeHole.allMoves_of _ ?_⟩
  intro mv
  by_cases hv : mv.next.val ≤ 3
  · simp [hv,kids_checked mv hv]
  · simp [hv]

def raw13Residuals : List (List Move × PartialMachine) :=
  residuals raw13 3 raw13Cut

theorem residual_count : raw13Residuals.length = {c["open"]} := by decide
theorem residual_mass : openMass 9 3 raw13Cut = {m["open"]} := by decide

theorem raw13_sound (m : Machine) (hm : TNFQuotientCompatible raw13 m) :
    WeightedBound 7014 m ∨
      ∃ e ∈ raw13Residuals, TNFQuotientCompatible e.2 m :=
  sound 7014 raw13 3 raw13Cut (by decide) raw13_support raw13_root raw13_nohalt cut_checked m hm

#print axioms cut_checked
#print axioms residual_count
#print axioms residual_mass
#print axioms raw13_sound
""")
    print("canonical candidate counts",dict(c))
    print("weighted ordinary-label mass",dict(m))
