"""Complete candidate tree for canonical raw107, B1=0RD.
The trusted verdict comes only from the generated Lean zipCheck proofs.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import sys, subprocess, json, hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as one
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import long_epoch
PARENT="1RB---_1RC0RD_0RD---_1LD1RE_---0RB_------"
BOUND=129
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
OVERRIDES="37:0012101 38:0012101"
def main():
    target=ROOT/"generated"; target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()=="498535eee6ac4a86e2deaf8b0297db04339047757a1e3f99a31b7e5700bab61c"
    opens=data.decode().splitlines()
    assert len(opens)==47==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["000"]*47
    for row in OVERRIDES.split():
        i,a=row.split(":");dfa[int(i)]=a
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false","namespace BB6.Agent6Raw107RDPumps","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for i in [0,2,3,30,36]:
        p=one.parse(opens[i])
        if i==3:
            ans=long_epoch.candidate(p,[e for e in one.concrete_events(p,3000) if e[0]>=1097],"L",4,1)
        else:
            ans=one.candidate(p,one.concrete_events(p,1500))
        assert ans is not None
        code,info=one.generate(i,p,ans)
        pumps[i]=f"BB6.Agent6Raw107RDPumps.M{i}"
        pumpcode.append(code)
        print(i,info)
    pumpcode.append("end BB6.Agent6Raw107RDPumps")
    (ROOT/"Raw107RDPumps.lean").write_text("\n\n".join(pumpcode)+"\n")
    ns="BB6.Agent6Raw107RD"
    def emit(name,imports,body):
        header=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
"""
        (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+header+body+f"\nend {ns}\n")
    tree=json.loads((target/"tree.json").read_text());stats=Counter()
    def build(node):
        tag,*v=node;stats[tag]+=1
        if tag=="cycle":
            e,k,r,b=v
            return f".cycle {e} {k} {str(r).lower()} ({b})"
        if tag=="last":
            n,s=v
            return f".last {n} {slot(s)}"
        if tag=="open":
            code=v[0];i=index[code]
            if i in pumps:return f".proven {pumps[i]}.table {pumps[i]}.never"
            a=dfa[i];rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,[int(ch,36) for ch in a[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        n,s,kids=v;assert len(kids)==24
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    assert tree[:3]==["split",15,8]
    bname="Raw107RDBase"
    emit(bname,["ZipThreeHoleAudit","Raw107RDPumps"],"""
abbrev p107 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,1⟩)
abbrev p107rd : PartialMachine := refine p107 (1,true) (some ⟨false,true,3⟩)
theorem p107rd_root : p107rd initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p107rd_nohalt : weightedTNFNoAssignedHalt p107rd :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine p107rd (4,false) (some mv)
theorem query : zipQueryOK 129 p107rd 15 (4,false) = true := by decide
""")
    mods=[]
    stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"Raw107RDKid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck 129 (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter({"cycle":7955,"last":1337,"open":47,"split":406}),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck 129 (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split 15 (4,false) kids
theorem tree_checked : zipCheck 129 p107rd tree = true := by
  change (zipQueryOK 129 p107rd 15 (4,false) && allMoves (fun mv => zipCheck 129 (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate 129 p107rd 6 :=
  certifiedZip 129 p107rd tree p107rd_root p107rd_nohalt tree_checked
theorem all_completions : ∀ m, compatible p107rd m → WeightedBound 129 m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
"""
    emit("Raw107RDData",mods,body)
    print(stats,"FAR",42,"pumps",5)
if __name__=="__main__": main()
