"""Reproduce the raw98 candidate audit and emit independently checked Lean declarations."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0LE"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o","enumerate"],cwd=ROOT,check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="c0d88308d8a306cba5430c9f2ecac67e739be2a0e425636f6ade33e579857bd1"
opens=raw.decode().splitlines()
assert len(opens)==98 and len(set(opens))==98
index={s:i for i,s in enumerate(opens)}
dfa={}
for row in (ROOT/"dfa.txt").read_text().split():
    i,a=row.split(":")
    dfa[int(i)]=a
pumps={
  2: ("1RB0RE_1RC1LF_0RD0RC_1LD1RE_0LA0LB_---0LE",".proven Unary.table Unary.never"),
  54:("1RB0RF_1RC1LF_0RD---_1LD1RE_1LF0LB_1RA0LE",".proven (Alternate.table false) (Alternate.never false)"),
  92:("1RB0RF_1RC1LF_0RD---_1LD1RE_1RD0LB_1RA0LE",".proven (Alternate.table true) (Alternate.never true)")}
assert set(dfa)|set(pumps)==set(range(98))
assert not set(dfa)&set(pumps)
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw98
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent19Raw98\n"
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+HEADER+body+FOOTER)
tree=json.loads((ROOT/"tree.json").read_text())
stats=Counter()
def build(node):
    tag,*v=node;stats[tag]+=1
    if tag=="cycle":
        e,k,r,b=v
        return f".cycle {e} {k} {str(r).lower()} ({b})"
    if tag=="last":
        n,s=v;return f".last {n} {slot(s)}"
    if tag=="open":
        code=v[0];i=index[code]
        if i in pumps:
            expected,proof=pumps[i]
            assert code==expected
            return proof
        a=dfa[i]
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",9,8]
emit("Raw98Base",["ThreeHoleAudit","Raw98Pump"],"""
abbrev p98 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,false,4⟩)
theorem p98_root : p98 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p98_nohalt : weightedTNFNoAssignedHalt p98 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
abbrev child98 (mv : Move) := refine p98 (4,false) (some mv)
theorem query98 : queryOK 442 p98 9 (4,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw98Kid{i:02}";mods.append(name)
    emit(name,["Raw98Base"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 442 (child98 {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=191,cycle=3421,last=898,open=98),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids98 : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids98_checked (mv : Move) : check 442 (child98 mv) (kids98 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree98 : Audit := .split 9 (4,false) kids98
theorem tree98_checked : check 442 p98 tree98 = true := by
  change (queryOK 442 p98 9 (4,false) && allMoves (fun mv => check 442 (child98 mv) (kids98 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query98, allMoves_of _ kids98_checked⟩
noncomputable def certificate98 : WeightedTNFCertificate 442 p98 6 :=
  certified 442 p98 tree98 p98_root p98_nohalt tree98_checked
theorem all98 : ∀ m, compatible p98 m → WeightedBound 442 m :=
  certificate98.sound

#print axioms tree98_checked
#print axioms all98
"""
emit("Raw98Data",mods,body)
print("Candidate tree:",stats,"FAR",len(dfa),"symbolic pumps",len(pumps))
