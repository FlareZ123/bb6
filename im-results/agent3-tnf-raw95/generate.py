"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
from generate_sweeps import candidate, concrete_events, generate
pump="1RB---_1RC1LF_0RD0RF_1LD1RE_0LE0LB_0LA0RD"
p=parse(pump)
ans=candidate(p,concrete_events(p))
assert ans is not None
proof,info=generate(95,p,ans)
assert info==(2,88,224)
(ROOT/"Raw95Sweep.lean").write_text("import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nnamespace BB6Coverage.Agent3SiblingPump\nopen BB6Coverage\n"+proof+"\nend BB6Coverage.Agent3SiblingPump\n")
PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RD"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o","enumerate"],cwd=ROOT,check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="8314e0a29ba36da0ba1cb97b63f23f54f07546dce19d03cc6f768ce3533e2759"
opens=raw.decode().splitlines()
assert len(opens)==53 and len(set(opens))==53
index={s:i for i,s in enumerate(opens)}
dfa=["00102030400"]*len(opens)
for row in (ROOT/"dfa.txt").read_text().split():
    i,a=row.split(":")
    dfa[int(i)]=a
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw95
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent3Raw95\n"
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
            return ".proven BB6Coverage.Agent3SiblingPump.M95.table BB6Coverage.Agent3SiblingPump.M95.never"
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",10,8]
emit("Raw95Base",["ThreeHoleAudit","Raw95Sweep"],"""
abbrev p95 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,3⟩)
theorem p95_root : p95 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p95_nohalt : weightedTNFNoAssignedHalt p95 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 6) firstOneCylinder_no_assigned_halt)
abbrev child95 (mv : Move) := refine p95 (4,false) (some mv)
theorem query95 : queryOK 395 p95 10 (4,false) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw95Kid{i:02}";mods.append(name)
    emit(name,["Raw95Base"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 395 (child95 {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=190,cycle=3542,last=799,open=53),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids95 : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids95_checked (mv : Move) : check 395 (child95 mv) (kids95 mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree95 : Audit := .split 10 (4,false) kids95
theorem tree95_checked : check 395 p95 tree95 = true := by
  change (queryOK 395 p95 10 (4,false) && allMoves (fun mv => check 395 (child95 mv) (kids95 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query95, allMoves_of _ kids95_checked⟩
noncomputable def certificate95 : WeightedTNFCertificate 395 p95 6 :=
  certified 395 p95 tree95 p95_root p95_nohalt tree95_checked
theorem all95 : ∀ m, compatible p95 m → WeightedBound 395 m :=
  certificate95.sound

#print axioms tree95_checked
#print axioms all95
"""
emit("Raw95Data",mods,body)
print("Candidate tree:",stats,"FAR",len(opens))
