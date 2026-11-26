"""Generate exact, kernel-checkable audits for independently closed Raw140 residuals.
Candidate enumeration uses existing cut.cpp and farbank.cpp, not trusted by Lean.
Run from repository root. Generated modules deliberately have disjoint table IDs.
"""
import concurrent.futures as cf
import json
from pathlib import Path
import subprocess as sp
import tempfile

DIR = Path(__file__).resolve().parent
BOUND = 10000

def parse(t):
    s=t.replace("_","")
    assert len(s)==36
    return [s[i:i+3] for i in range(0,36,3)]

def bits(x):
    while x:
        b=x & -x
        yield b.bit_length()-1
        x-=b

def far_data(table,code):
    rev=bool(int(code[0]))
    dfa=list(map(int,code[1:]))
    d=len(dfa)//2
    assert len(dfa)==2*d and d>0 and dfa[0]==0 and max(dfa)<d
    N=6*d+1
    H=N-1
    halt=1<<H
    T=[0]*(2*N)
    T[H]=T[N+H]=halt
    rules=[]
    p=parse(table)
    for l in range(d):
        for q in range(6):
            for a in range(2):
                dst=a*N+6*l+q
                x=p[2*q+a]
                if x=="---":
                    T[dst]=halt
                    continue
                w,r,nxt=int(x[0]),x[1]=="R",ord(x[2])-65
                if r!=rev:
                    T[dst]=1<<(6*dfa[2*l+w]+nxt)
                else:
                    rules.extend((dst,b*N+6*j+nxt,w*N) for j in range(d) for b in range(2) if dfa[2*j+b]==l)
    while True:
        z=halt
        while True:
            old=z
            for j in range(N):
                if T[j]&z:z|=1<<j
            assert not z&1, (table,code)
            if z==old:break
        changed=False
        for dst,src,off in rules:
            v=T[dst]
            for j in bits(T[src]):v|=T[off+j]
            if v!=T[dst]:
                T[dst]=v
                changed=True
        if not changed:break
    return f".far {str(rev).lower()} {d} ⟨0, {dfa}, {T[:N]}, {T[N:]}, {z}⟩"

def slot(s):
    return f"({s//2},{str(bool(s%2)).lower()})"

def emit(t,far):
    k=t[0]
    if k=="cycle":
        _,e,p,r,b=t
        return f".cycle {e} {p} {str(bool(r)).lower()} ({b})"
    if k=="last":return f".last {t[1]} {slot(t[2])}"
    if k=="open":return far_data(t[1],far[t[1]])
    if k=="split":
        assert len(t[3])==24
        return f".split {t[1]} {slot(t[2])} (byMove [\n"+",\n".join(emit(c,far) for c in t[3])+"\n])"
    raise ValueError(t)

HEADER="""import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw140Deep
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent50TNFPilot
"""

def theorem(i,table,tree,far):
    codes=[24 if a=="---" else 4*(ord(a[2])-65)+2*int(a[0])+int(a[1]=="R") for a in parse(table)]
    return f"""
namespace R{i}
def p : PartialMachine := FAR.fromCodes {codes}
def audit : Audit := {emit(tree,far)}
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem checked : zipCheck {BOUND} p audit = true := by decide +kernel
theorem cover : Cover (WeightedBound {BOUND}) p :=
  (certifiedZip {BOUND} p audit root nohalt checked).toCover
#print axioms cover
end R{i}
"""

def main():
    residuals=json.loads((DIR/"raw140-residuals.json").read_text())["residuals"]
    roots=[(i,t) for i,t in enumerate(residuals) if t.count("---") in (1,2)]
    assert len(roots)==180
    with tempfile.TemporaryDirectory() as tmp:
        d=Path(tmp)
        sp.run(["g++","-O3","-std=c++20","im-results/agent7-raw49/cut.cpp","-o",str(d/"cut")],check=True)
        sp.run(["g++","-O3","-std=c++20","im-results/agent19-raw40-cut/farbank.cpp","-o",str(d/"farbank")],check=True)
        def classify(row):
            i,t=row
            p=d/str(i)
            sp.run([str(d/"cut"),t,"10000","32","3",str(p)],check=True,stdout=sp.DEVNULL)
            return i,t,json.loads(p.with_suffix(".json").read_text()),p.with_suffix(".open").read_text().splitlines()
        with cf.ThreadPoolExecutor(max_workers=4) as pool:
            results=list(pool.map(classify,roots))
        opens=list(dict.fromkeys(o for _,_,_,os in results for o in os))
        bank_input="".join(f"{i} {t.replace('_','')}\n" for i,t in enumerate(opens))
        bank=sp.run([str(d/"farbank"),"5"],input=bank_input,text=True,capture_output=True,check=True)
        far={opens[int(i)]:c for i,c in (line.split() for line in bank.stdout.splitlines())}
        closed=[(i,t,tree) for i,t,tree,os in results if all(o in far for o in os)]
        pending=[{"id":i,"table":t,"open":[o for o in os if o not in far]} for i,t,_,os in results if any(o not in far for o in os)]
        expected={1:36,2:93}
        counts={h:sum(t.count("---")==h for _,t,_ in closed) for h in (1,2)}
        assert counts==expected,counts
        print("closed",counts,"pending",len(pending),"FAR",len(far),"/",len(opens))
        names=[]
        for offset in range(0,len(closed),12):
            group=closed[offset:offset+12]
            name=f"Raw140Deep{offset//12:02}"
            names.append(name)
            (DIR/(name+".lean")).write_text(HEADER+"".join(theorem(i,t,tree,far) for i,t,tree in group)+"\nend BB6.Agent10Raw140Deep\n")
        # An explicit proof-bearing roster. Each entry uses its independently checked theorem.
        body="".join(f"import {n}\n" for n in names)+"""
namespace BB6.Agent10Raw140Deep
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
structure Closed where
  table : PartialMachine
  safe : Cover (WeightedBound 10000) table
def closed : List Closed := [
"""+",\n".join(f"  ⟨R{i}.p, R{i}.cover⟩" for i,_,_ in closed)+"""
]
theorem closed_count : closed.length = 129 := by decide
theorem matches_sound (p : PartialMachine)
    (h : closed.any (fun c => tableOK p c.table) = true) :
    Cover (WeightedBound 10000) p := by
  obtain ⟨c, _, hc⟩ := List.any_eq_true.mp h
  have he := tableOK_sound p c.table hc
  rw [he]
  exact c.safe
#print axioms matches_sound
end BB6.Agent10Raw140Deep
"""
        (DIR/"Raw140DeepCovers.lean").write_text(body)
        (DIR/"raw140-deep-summary.json").write_text(json.dumps({"bound":BOUND,"closed": [{"id":i,"table":t} for i,t,_ in closed],"pending":pending,"far":far},indent=2)+"\n")

if __name__=="__main__":main()
