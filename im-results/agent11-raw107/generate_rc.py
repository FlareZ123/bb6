"""Complete candidate tree for canonical raw107, B1=0RC.
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
PARENT="1RB---_1RC0RC_0RD---_1LD1RE_---0RB_------"
BOUND=200
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
GROUPS="""00101 0,32,41,48,49,50,52,53,56,73,80,81,82,83,87,92,97,114,118,120,121,122,123,124,188,254,279,280,284,285,286,288,289,290,297,298,304,308,309,310,315,316,318,328,332,336,339,340,342,345,356,359,374,385
0010202 2,3
101213333 14
0012101 63,64,65,111,190,236,237,238,239,243,271
100 88,89,90,116,197,203,204,205,206,247,249,250,251,334,335,337,338,347
0012111 127
0012110 139,145,172,173
00121342144 181,182,201,208,355,361,364,371,386
001213020 200
10101 262
001230123 263
10121343322 265,266,354
001213101 277
0012322415241 349,353,376,389
005312464243135 350
001211321 351
1012344514444 375"""
def main():
    target=ROOT/"generated_rc"; target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()=="9d6ea5784163259089bd5f03f627ffc8ecd8d5bfe361a07c7be7bdeefcd25551"
    opens=data.decode().splitlines()
    assert len(opens)==392==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["000"]*392
    for row in GROUPS.splitlines():
        a,ids=row.split()
        for i in ids.split(","): dfa[int(i)]=a
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false","namespace BB6.Agent11Raw107RCPumps","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for i in [102]:
        p=one.parse(opens[i]);ans=one.candidate(p,one.concrete_events(p,1500))
        assert ans is not None
        code,info=one.generate(i,p,ans)
        pumps[i]=f"BB6.Agent11Raw107RCPumps.M{i}"
        pumpcode.append(code)
        print(i,info)
    pumps[100]="BB6.Agent11Raw107RCCountdown"
    assert opens[100]=="1RB0RF_1RC0RC_0RD0RA_1LD1RE_---0RB_0RC0LD"
    pumpcode.append("end BB6.Agent11Raw107RCPumps")
    (ROOT/"Raw107RCPumps.lean").write_text("\n\n".join(pumpcode)+"\n")
    ns="BB6.Agent11Raw107RC"
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
    assert tree[:3]==["split",16,5]
    bname="Raw107RCBase"
    emit(bname,["ZipThreeHoleAudit","Raw107RCPumps","Raw107RCCountdown"],"""
abbrev p107 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,1⟩)
abbrev p107rc : PartialMachine := refine p107 (1,true) (some ⟨false,true,2⟩)
theorem p107rc_root : p107rc initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p107rc_nohalt : weightedTNFNoAssignedHalt p107rc :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine p107rc (2,true) (some mv)
theorem query : zipQueryOK 200 p107rc 16 (2,true) = true := by decide
""")
    mods=[]
    stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"Raw107RCKid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck 200 (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter({"cycle":19427,"last":3343,"open":392,"split":1007}),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck 200 (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split 16 (2,true) kids
theorem tree_checked : zipCheck 200 p107rc tree = true := by
  change (zipQueryOK 200 p107rc 16 (2,true) && allMoves (fun mv => zipCheck 200 (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate 200 p107rc 6 :=
  certifiedZip 200 p107rc tree p107rc_root p107rc_nohalt tree_checked
theorem all_completions : ∀ m, compatible p107rc m → WeightedBound 200 m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
"""
    emit("Raw107RCData",mods,body)
    print(stats,"FAR",390,"pumps",2)
if __name__=="__main__": main()
