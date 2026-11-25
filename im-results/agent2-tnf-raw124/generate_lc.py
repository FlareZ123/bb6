"""Replay the exact candidate search; emit checked Lean modules, never trust a cutoff."""
from pathlib import Path
import sys, json, hashlib, subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
PARENT="1RB---_1RC---_0RD---_1LD1RE_---1LF_---0LC"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99"/"enumerate.cpp"),"-o",str(ROOT/"enumerate")],check=True)
subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=ROOT,check=True)
raw=(ROOT/"open.txt").read_bytes()
assert hashlib.sha256(raw).hexdigest()=="6efd8ce1d52920d5282b9e4e65e97d7edbed6b1232f325550945e30ae8574f8f5"
opens=raw.decode().splitlines()
assert len(opens)==282 and len(set(opens))==282
index={s:i for i,s in enumerate(opens)}
subprocess.run(["g++","-std=c++20","-O3",str(ROOT.parent/"agent11-tnf-raw86"/"search.cpp"),"-o",str(ROOT/"search")],check=True)
inp="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens) if i not in {97,126})
out=subprocess.run([str(ROOT/"search"),"6"],input=inp,text=True,capture_output=True,check=True)
print(out.stderr)
dfa=dict((int(i),v) for i,v in (line.split() for line in out.stdout.splitlines()))
assert set(dfa)==set(range(282))-{97,126}
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124LC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
"""
FOOTER="\nend BB6.Agent2Raw124LC\n"
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+HEADER+body+FOOTER)
body="""open BB6Coverage.Agent50Pump
def fromRows (xs : List (Option (Option Move))) : PartialMachine :=
  fun s => (xs[2*s.1.val+s.2.toNat]?).getD none
"""
for i,entry,q,pre,block,post,opspec in [
    (126,10,0,"110","110110","11","5 R2,8,111111 16 L0,6,110110 3"),
    (97,34,5,"1110","111110111110","1111","8 R1,28,101111101111 29 L0,20,111011111011 16 R1,28,111011111011 45 L0,20,101111101111 12 R2,28,111101111101 62 L1,20,111110111110 3")
]:
    table="["+",".join("none" if a=="---" else "some (some "+move(a)+")" for a in parse(opens[i]))+"]"
    ops=[]
    for x in opspec.split():
        if x.isdigit(): ops.extend([".step"]*int(x))
        else:
            k,c,v=x[1:].split(",")
            ops.append(f'.{"left" if x[0]=="L" else "right"} {k} {c} (bits "{v}")')
    body+=f"""
def pumpTable{i} : PartialMachine := fromRows {table}
def pumpCert{i} : Certificate := ⟨{entry},⟨{q},(word "" "" ""),(word "{pre}" "{block}" "{post}")⟩,[{",".join(ops)}]⟩
theorem pumpCheck{i} : pumpCert{i}.check pumpTable{i} = true := by decide
theorem pumpNever{i} : ∀ m, compatible pumpTable{i} m → NeverHalts m :=
  Certificate.never pumpTable{i} pumpCert{i} pumpCheck{i}
#print axioms pumpNever{i}
"""
emit("Raw124LCPumps",["ThreeHoleAudit","BlockPump"],body)
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
        if i in {97,126}:return f".proven pumpTable{i} pumpNever{i}"
        a=dfa[i]
        rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
        return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
    assert tag=="split"
    n,s,kids=v;assert len(kids)==24
    return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
assert tree[:3]==["split",8,5]
emit("Raw124LCBase",["Raw124LCPumps"],"""
abbrev p124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev p0LC : PartialMachine :=
  refine p124 (5,true) (some ⟨false,false,2⟩)
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem p0LC_root : p0LC initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p0LC_nohalt : weightedTNFNoAssignedHalt p0LC :=
  weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt
abbrev child0LC (mv : Move) := refine p0LC (2,true) (some mv)
theorem query0LC : queryOK 145 p0LC 8 (2,true) = true := by decide
""")
mods=[]
for i,kid in enumerate(tree[3]):
    name=f"Raw124LCKid{i:02}";mods.append(name)
    emit(name,["Raw124LCBase"],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check 145 (child0LC {move(MOVES[i])}) kid{i:02} = true := by decide
""")
assert stats==Counter(split=1375,cycle=26097,last=5270,open=282),stats
cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
body="""
def kids0LC : Move → Audit := byMove ["""+",".join(f"kid{i:02}" for i in range(24))+"""]
theorem kids0LC_checked (mv : Move) : check 145 (child0LC mv) (kids0LC mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+cases+"""
def tree0LC : Audit := .split 8 (2,true) kids0LC
theorem tree0LC_checked : check 145 p0LC tree0LC = true := by
  change (queryOK 145 p0LC 8 (2,true) && allMoves (fun mv => check 145 (child0LC mv) (kids0LC mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query0LC, allMoves_of _ kids0LC_checked⟩
noncomputable def certificate0LC : WeightedTNFCertificate 145 p0LC 6 :=
  certified 145 p0LC tree0LC p0LC_root p0LC_nohalt tree0LC_checked
theorem all0LC : ∀ m, compatible p0LC m → WeightedBound 145 m :=
  certificate0LC.sound

#print axioms tree0LC_checked
#print axioms all0LC
"""
emit("Raw124LCData",mods,body)
print("Candidate tree:",stats)
