"""Disjoint three-hole parent cut, using original Lean partialAudit checker.

Candidate enumeration and FAR saturation are untrusted. All selected leaves and
all first queries are checked by Lean. Long growth proofs use the already
accepted modules; upstream id36 is discharged through an exact source bridge. Run from repository root.
"""
from pathlib import Path
import sys
import json, subprocess as sp, tempfile
from generate_raw140_deep import far_data, slot, parse
DIR=Path(__file__).resolve().parent
PARENT="1RB---_1RC0LD_1RD0RA_1LB1LE_0LB0RE_------"
B=10010
def literal(a,f):
    def mv(c): return f"{(c//2)%2}{'R' if c%2 else 'L'}{chr(65+c//4)}"
    return PARENT.replace("1RB---","1RB"+mv(a)).replace("------",mv(f)+"---")
PROVEN={}
for i,(a,f) in enumerate([(21,4),(21,8),(21,1),(23,16),(23,6),(23,3),(23,15)]):
    PROVEN[literal(a,f)]=f"Raw140Orbit.V{i}"
PROVEN[literal(21,16)]="Raw140Extra.X11"
for i,a,f in [(34,21,5),(38,21,2),(75,23,12),(78,23,5),(79,23,9)]:
    PROVEN[literal(a,f)]=f"Raw140Long.X{i}"
SOURCE = "--source36" in sys.argv
if SOURCE: PROVEN[literal(21,13)]="Raw14036"
for f in (4,13):
    PROVEN[literal(23,f)]=f"Raw140Double.X{f}"

def main():
    with tempfile.TemporaryDirectory() as tmp:
        d=Path(tmp)
        sp.run(["g++","-O3","-std=c++20","im-results/agent7-raw49/cut.cpp","-o",str(d/"cut")],check=True)
        sp.run(["g++","-O3","-std=c++20","im-results/agent19-raw40-cut/farbank.cpp","-o",str(d/"farbank")],check=True)
        sp.run([str(d/"cut"),PARENT,"10000","32","3",str(d/"tree")],check=True)
        tree=json.loads((d/"tree.json").read_text())
        opens=(d/"tree.open").read_text().splitlines()
        assert len(opens)==len(set(opens))==89
        inp="".join(f"{i} {t.replace('_','')}\n" for i,t in enumerate(opens) if t not in PROVEN)
        p=sp.run([str(d/"farbank"),"5"],input=inp,text=True,capture_output=True,check=True)
        far={opens[int(i)]:c for i,c in (l.split() for l in p.stdout.splitlines())}
        print("FAR hits",len(far),"known",len(PROVEN),flush=True)
    assert set(PROVEN)<=set(opens)
    pending=[]
    def emit(t):
        k=t[0]
        if k=="cycle":
            _,e,p,r,b=t
            return f".closed (.cycle {e} {p} {str(bool(r)).lower()} ({b}))"
        if k=="last": return f".closed (.last {t[1]} {slot(t[2])})"
        if k=="split":
            return f".split {t[1]} {slot(t[2])} (byPartialMove [\n"+",\n".join(emit(c) for c in t[3])+"\n])"
        assert k=="open",t
        p=t[1]
        if p in PROVEN:
            n=PROVEN[p]
            return f".closed (.proven {n}.p {n}.never)"
        if p in far: return ".closed ("+far_data(p,far[p])+")"
        pending.append(p)
        return ".unresolved"
    body=emit(tree)
    assert len(far)==54 and len(PROVEN)==15+int(SOURCE) and len(pending)==20-int(SOURCE), (len(far),len(PROVEN),len(pending))
    assert all(t.count("---")==1 for t in pending)
    codes=[24 if a=="---" else 4*(ord(a[2])-65)+2*int(a[0])+int(a[1]=="R") for a in parse(PARENT)]
    out="""import PartialAudit
import Raw140SevenCover
import Raw140ExtraNovelCover
import Raw140LongFourCover
import Raw140Long79Cover
import Raw140DoubleCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw140ThreeHole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6.Agent50TNFPilot
"""
    if SOURCE: out = out.replace("import Raw140DoubleCover\n", "import Raw140DoubleCover\nimport Raw14036Cover\n")
    out+=f"""
def parent : PartialMachine := FAR.fromCodes {codes}
def tree : PartialAudit := {body}
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem checked : partialCheck {B} parent tree = true := by decide +kernel
def remaining := partialResiduals parent tree
theorem remaining_count : remaining.length = {len(pending)} := by decide +kernel
theorem sound : ∀ m, compatible parent m → WeightedBound {B} m ∨
  ∃ e ∈ remaining, compatible e.2 m :=
  partialSound {B} parent tree root nohalt checked
theorem cover {{N : Nat}} (hN : {B} ≤ N)
    (h : ∀ e ∈ remaining, Cover (WeightedBound N) e.2) :
    Cover (WeightedBound N) parent := by
  apply Cover.leaf
  intro m hm
  rcases sound m hm with hb | ⟨e,he,hq⟩
  · intro k d hk hd; exact Nat.le_trans (hb k d hk hd) hN
  · exact (h e he).sound m hq
#print axioms checked
#print axioms remaining_count
#print axioms sound
#print axioms cover
end BB6.Agent10Raw140ThreeHole
"""
    (DIR/"Raw140ThreeHoleCut.lean").write_text(out)
    (DIR/"raw140-three-hole-pending.json").write_text(json.dumps({"parent":PARENT,"bound":B,"open":len(opens),"far":len(far),"known":PROVEN,"remaining":[{"id":opens.index(t),"table":t} for t in pending]},indent=2)+"\n")
    print("pending",[(opens.index(t),t) for t in pending],flush=True)
if __name__=="__main__":main()
