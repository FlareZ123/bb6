"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
from generate_sweeps import candidate, concrete_events, generate
pump="1RB---_1RC1LF_0RD0RC_1LD1RE_0LA0LB_1LE1RF"
p=parse(pump)
ans=candidate(p,concrete_events(p))
assert ans is not None
proof,info=generate(105,p,ans)
assert info==(13,39,40)
(ROOT/"Raw105Sweep.lean").write_text("import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nnamespace BB6Coverage.Agent3SiblingPump\nopen BB6Coverage\n"+proof+"\nend BB6Coverage.Agent3SiblingPump\n")
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RF"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o","enumerate"],cwd=ROOT,check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="1b3a9a1f6a1aff496874f719d4df2db74b72c6800ccd23508de8c05ce67db1fc"
opens=raw.decode().splitlines()
assert len(opens)==77 and len(set(opens))==77
index={s:i for i,s in enumerate(opens)}
dfa=["00102030400"]*len(opens)
for row in (ROOT/"dfa.txt").read_text().split():
    i,a=row.split(":")
    dfa[int(i)]=a
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw105
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent3Raw105\n"
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
        code=v[0];i=index[code];a=dfa[i]
        if a=="-":
            assert code==pump
            return ".proven BB6Coverage.Agent3SiblingPump.M105.table BB6Coverage.Agent3SiblingPump.M105.never"
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",10,10]
emit("Raw105Base",["ThreeHoleAudit","Raw105Sweep"],"""
abbrev p105 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨true,true,5⟩)
theorem p105_root : p105 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p105_nohalt : weightedTNFNoAssignedHalt p105 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
abbrev child105 (mv : Move) := refine p105 (5,false) (some mv)
theorem query105 : queryOK 395 p105 10 (5,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw105Kid{i:02}";mods.append(name)
    emit(name,["Raw105Base"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 395 (child105 {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=121,cycle=2280,last=450,open=77),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids105 : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids105_checked (mv : Move) : check 395 (child105 mv) (kids105 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree105 : Audit := .split 10 (5,false) kids105
theorem tree105_checked : check 395 p105 tree105 = true := by
  change (queryOK 395 p105 10 (5,false) && allMoves (fun mv => check 395 (child105 mv) (kids105 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query105, allMoves_of _ kids105_checked⟩
noncomputable def certificate105 : WeightedTNFCertificate 395 p105 6 :=
  certified 395 p105 tree105 p105_root p105_nohalt tree105_checked
theorem all105 : ∀ m, compatible p105 m → WeightedBound 395 m :=
  certificate105.sound

#print axioms tree105_checked
#print axioms all105
"""
emit("Raw105Data",mods,body)
print("Candidate tree:",stats,"FAR",len(opens))
