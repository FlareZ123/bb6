#!/usr/bin/env python3
"""Generate the canonical raw13 partial audit. Only Lean checker acceptance
can certify the output. No time limit is used as evidence of nonhalting."""
from collections import Counter
from itertools import product
from pathlib import Path
import subprocess
import tempfile
import json
import importlib.util

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

def timeout_tables(t,p):
    if t[0] == "split":
        _,_,s,kids = t
        for mv,k in zip(MOVES,kids):
            if k is not None:
                c = p[:]
                c[s] = mv
                yield from timeout_tables(k,c)
    elif t[0] == "open" and scan(p)[0] == "timeout":
        yield "".join(v or "---" for v in p)

def enhance(t,p,proven):
    if t[0] == "split":
        n,s,kids = t[1:]
        children = []
        for mv,k in zip(MOVES,kids):
            if k is None:
                children.append(None)
            else:
                c = p[:]
                c[s] = mv
                children.append(enhance(k,c,proven))
        return ("split",n,s,children)
    if t[0] == "open":
        raw = "".join(v or "---" for v in p)
        if raw in proven:
            return proven[raw]
        if raw == "1RB1LC1RC0LD1LA0RB1LB1LE1RF1LA---0RE":
            return ("last",121,10)
    return t

def build_enhanced(t):
    hard = list(timeout_tables(t,ROOT))
    assert len(hard) == 20 and len(set(hard)) == 20
    ng = D.parent/"agent1-ngram"
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        data = tmp/"tables.txt"
        data.write_text("".join(f"{i} {raw}\n" for i,raw in enumerate(hard)))
        binpath = tmp/"ngram"
        subprocess.run(["g++","-std=c++17","-O3",str(ng/"ngram.cpp"),"-o",str(binpath)],check=True)
        certs = tmp/"certs.txt"
        with data.open("r") as inp, certs.open("w") as out:
            subprocess.run([str(binpath),"6"],stdin=inp,stdout=out,check=True)
        subprocess.run(["python",str(ng/"emit_ngram.py"),str(data),str(certs),
            str(D/"Agent46Raw13NGram.lean"),"--namespace","BB6.Agent46Raw13NGram"],check=True)
        ids = [int(line.split()[0]) for line in certs.read_text().splitlines()]
    assert len(ids) == 15, ids
    proven = {hard[i]:("ngram",i) for i in ids}
    pumps = {
        "1RB0LD1RC1RA1LA------1LA------------":0,
        "1RB1LC1RC0LD1LA0RB1LB1LE1RF0RA---0RE":12,
        "1RB1LC1RC0LD1LA0RB1LB1LE1RF0RD---0RE":14,
    }
    assert set(pumps) <= set(hard) and not (set(proven) & set(pumps))
    proven.update({raw:("pump",i) for raw,i in pumps.items()})
    return enhance(t,ROOT,proven)

def enhance_selected(t):
    """Close 19 exact residual cylinders with exhaustive canonical subtrees."""
    ng = D.parent/"agent1-ngram"
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        binpath = tmp/"selected"
        subprocess.run(["g++","-std=c++17","-O3",str(D/"select_complete.cpp"),"-o",str(binpath)],check=True)
        with (D/"selected.txt").open() as inp:
            proc = subprocess.run([str(binpath)],stdin=inp,text=True,capture_output=True)
        assert proc.returncode == 0, proc.stderr
        selected = {raw:json.loads(data) for raw,data in (line.split(" ",1) for line in proc.stdout.splitlines())}
        assert len(selected)==19
        grams = []
        def collect(t):
            if t[0]=="ngram":
                grams.append(t[1])
            elif t[0]=="split":
                for c in t[3]:
                    if c is not None: collect(c)
        for sub in selected.values(): collect(sub)
        assert len(grams)==826
        assert len(set(grams))==826
        data = tmp/"tables.txt"
        data.write_text("".join(f"{100+i} {raw}\n" for i,raw in enumerate(grams)))
        ngram = tmp/"ngram"
        subprocess.run(["g++","-std=c++17","-O3",str(ng/"ngram.cpp"),"-o",str(ngram)],check=True)
        certs = tmp/"certs.txt"
        with data.open() as inp, certs.open("w") as out:
            subprocess.run([str(ngram),"7"],stdin=inp,stdout=out,check=True)
        assert len(certs.read_text().splitlines())==826
        all_lines = certs.read_text().splitlines()
        names = []
        for i in range(0,len(all_lines),16):
            name=f"Agent46Raw13SelectedGram{i//16}"
            names.append(name)
            shard = tmp/"shard.txt"
            shard.write_text("\n".join(all_lines[i:i+16])+"\n")
            subprocess.run(["python",str(ng/"emit_ngram.py"),str(data),str(shard),
                str(D/(name+".lean")),"--namespace","BB6.Agent46Raw13SelectedGram"],check=True)
        (D/"Agent46Raw13SelectedGram.lean").write_text("".join(f"import {n}\n" for n in names))
        # Reuse Agent47's sparse kernel checker and trie emitter at width 14.
        sparse_dir = D.parent/"agent47-raw111-cut"
        sparse_exe = tmp/"ngram_sparse"
        subprocess.run(["g++","-O3","-std=c++17",str(sparse_dir/"ngram_sparse.cpp"),"-o",str(sparse_exe)],check=True)
        raw = "1RB1LC1RC0LD1LA0RB1LB1RE0RF0RA---0RD"
        out = subprocess.check_output([str(sparse_exe),"14"],input=f"0 {raw}\n",text=True)
        i,data = out.strip().split(maxsplit=1)
        assert i=="0"
        spec = importlib.util.spec_from_file_location("shared_sparse_emitter",sparse_dir/"emit_sparse.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        module.emit(D,0,raw,data,width=14,module_name="Agent46Raw13Sparse1RE",expected=(1405,88,448))
        ids={raw:100+i for i,raw in enumerate(grams)}
        def norm(t):
            if t[0]=="ngram": return ("selectedgram",ids[t[1]])
            if t[0]=="split": return ("split",t[1],t[2],[norm(c) if c is not None else None for c in t[3]])
            return tuple(t)
        return enhance(t,ROOT,{raw:norm(sub) for raw,sub in selected.items()})

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
    if tag == "ngram":
        i = v[0]
        return f".closed (.proven BB6.Agent46Raw13NGram.p{i} BB6.Agent46Raw13NGram.never{i})"
    if tag == "sparse1RE":
        n = "BB6.Agent47SparseNGram.Agent46Raw13Sparse1RE"
        return f".closed (.proven {n}.table {n}.never)"
    if tag == "pump1RE2":
        n = "BB6Coverage.Agent31Pump.Raw13Pump1RE2"
        return f".closed (.proven {n}.table {n}.never)"
    if tag == "pump0LC":
        n = "BB6Coverage.Agent31Pump.Raw13Pump0LC"
        return f".closed (.proven ({n}.table {v[0]}) ({n}.never {v[0]} (by decide)))"
    if tag == "pump0RD":
        n = "BB6Coverage.Agent31Pump.Raw13Pump0RD"
        return f".closed (.proven ({n}.table {v[0]}) ({n}.never {v[0]} (by decide)))"
    if tag == "pump0RC":
        n = "BB6Coverage.Agent31Pump.Raw13Pump0RC"
        return f".closed (.proven {n}.table {n}.never)"
    if tag == "pump0RE":
        n = "BB6Coverage.Agent31Pump.Raw13Pump0RE"
        return f".closed (.proven ({n}.table {v[0]}) ({n}.never {v[0]} (by decide)))"
    if tag == "late0RE":
        n = "BB6Coverage.Agent31Pump.Raw13Late0RE"
        return f".bounded {n}.table 21269 {n}.bound"
    if tag in ("zeroRCparent","zeroRDparent"):
        n = "BB6.Agent46Raw13Zero"+tag[4:6]
        return f".bounded {n}.parent 7014 {n}.bound"
    if tag == "zeroREparent":
        n = "BB6.Agent46Raw13ZeroRE"
        return f".bounded {n}.parent 21269 {n}.bound"
    if tag == "pump0LE":
        n = "BB6Coverage.Agent31Pump.Raw13Pump0LE"
        return f".closed (.proven {n}.table {n}.never)"
    if tag == "pump1RE":
        n = "BB6Coverage.Agent31Pump.Raw13Pump1RE"
        return f".closed (.proven {n}.table {n}.never)"
    if tag == "sharedpump":
        n = "BB6Coverage.Agent31Pump.Raw13Shared"
        suffix = v[0][24:27]
        assert suffix in ("0RE","0RF","1LF")
        return f".closed (.proven {n}.table{suffix} {n}.never{suffix})"
    if tag == "selectedgram":
        i=v[0]
        return f".closed (.proven BB6.Agent46Raw13SelectedGram.p{i} BB6.Agent46Raw13SelectedGram.never{i})"
    if tag == "pump":
        n = f"BB6Coverage.Agent31Pump.Raw13Pump{v[0]}"
        return f".closed (.proven {n}.table {n}.never)"
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
    t = enhance_selected(build_enhanced(t))
    t = enhance(t,ROOT,{"1RB1LC1RC0LD1LA0RB1LB0RE------------":("zeroREparent",),
        "1RB1LC1RC0LD1LA0RB0RC---------------":("zeroRCparent",),
        "1RB1LC1RC0LD1LA0RB0RD---------------":("zeroRDparent",)})
    c,m = Counter(),Counter()
    tally(t,9,3,c,m)
    assert c == Counter(open=1719,cycle=2708,state=948,split=353,halt=353,last=999,ngram=15,pump=3,selectedgram=826,pump1RE=1,sharedpump=3,pump0LE=1,pump1RE2=1,sparse1RE=1,zeroREparent=1,zeroRCparent=1,zeroRDparent=1),c
    assert m["open"] == 1725351562650 and sum(m.values()) == 25**9,m
    names = []
    for i,k in enumerate(t[3]):
        if k is None:
            continue
        name = f"Agent46Raw13Kid{i:02}"
        names.append(name)
        mv = move(MOVES[i])
        write(name,["Agent46Raw13Base","Agent46Raw13NGram","Agent46Raw13Pumps","Agent46Raw13SelectedGram","Agent46Raw13Pump1RE","Agent46Raw13SharedPumps","Agent46Raw13Pump0LE","Agent46Raw13Pump1RE2","Agent46Raw13Sparse1RE","Agent46Raw13ZeroRE","Agent46Raw13ZeroRC","Agent46Raw13ZeroRD"],f"""
def kid{i:02} : Cut := {emit(k)}
theorem checked{i:02} :
    check 21269 (child {mv}) (nextCut 3 {mv}) kid{i:02} = true := by decide
""")
    terms = ",".join(f"kid{i:02}" if k is not None else ".unresolved" for i,k in enumerate(t[3]))
    cases = "\n".join(f"  · exact checked{12*w+6*r+q:02}" for q,w,r in product(range(4),range(2),range(2)))
    write("Agent46Raw13Data",names,f"""
def kids : Move → Cut := byCutMove [{terms}]
theorem kids_checked (mv : Move) (hv : mv.next.val ≤ 3) :
    check 21269 (child mv) (nextCut 3 mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  change q.val ≤ 3 at hv
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hq with rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}

def raw13Cut : Cut := .split 3 (0,true) kids

theorem cut_checked : check 21269 raw13 3 raw13Cut = true := by
  change (BB6.Agent10ZipAudit.zipQueryOK 21269 raw13 3 (0,true) &&
    BB6.Agent31ThreeHole.allMoves (fun mv =>
      if mv.next.val ≤ 3 then check 21269 (child mv) (nextCut 3 mv) (kids mv)
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
    WeightedBound 21269 m ∨
      ∃ e ∈ raw13Residuals, TNFQuotientCompatible e.2 m :=
  sound 21269 raw13 3 raw13Cut (by decide) raw13_support raw13_root raw13_nohalt cut_checked m hm

#print axioms cut_checked
#print axioms residual_count
#print axioms residual_mass
#print axioms raw13_sound
""")
    print("canonical candidate counts",dict(c))
    print("weighted ordinary-label mass",dict(m))
