"""Complete candidate tree for canonical raw107, B1=0RE.
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
PARENT="1RB---_1RC0RE_0RD---_1LD1RE_---0RB_------"
BOUND=201
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
GROUPS="""00101 0,4,29,38,72,105,156,158,161,162,163,170,201,202,203,216,234,251,252
0010202 1,85,88,123,124,125,130,140,157,159,168,169,206,228,238,250
001210321 2
0012101 18
10101 19
001230123 33
101213333 57,211
100 79,97,102,103,134,135,136
001230323 114
10121232421 120
001213121 146
001020303 219
00121342144 229"""
def main():
    target=ROOT/"generated_re"; target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()=="775e6212f0fee97c622a3e7df398cb232b843a4e5b4a5a4e96e0158228b7222b"
    opens=data.decode().splitlines()
    assert len(opens)==258==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["000"]*258
    for row in GROUPS.splitlines():
        a,ids=row.split()
        for i in ids.split(","): dfa[int(i)]=a
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false","namespace BB6.Agent11Raw107REPumps","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for i in [23,41,184,190,191,199]:
        p=one.parse(opens[i]);ans=one.candidate(p,one.concrete_events(p,1500))
        assert ans is not None
        code,info=one.generate(i,p,ans)
        pumps[i]=f"BB6.Agent11Raw107REPumps.M{i}"
        pumpcode.append(code)
        print(i,info)
    pumps[7]="BB6.Agent11Raw107RECounter"
    assert opens[7]=="1RB1LF_1RC0RE_0RD---_1LD1RE_0LF0RB_1LA0LB"
    pumpcode.append("end BB6.Agent11Raw107REPumps")
    (ROOT/"Raw107REPumps.lean").write_text("\n\n".join(pumpcode)+"\n")
    ns="BB6.Agent11Raw107RE"
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
    assert tree[:3]==["split",8,8]
    bname="Raw107REBase"
    emit(bname,["ZipThreeHoleAudit","Raw107REPumps","Raw107RECounter"],"""
abbrev p107 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,1⟩)
abbrev p107re : PartialMachine := refine p107 (1,true) (some ⟨false,true,4⟩)
theorem p107re_root : p107re initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p107re_nohalt : weightedTNFNoAssignedHalt p107re :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine p107re (4,false) (some mv)
theorem query : zipQueryOK 201 p107re 8 (4,false) = true := by decide
""")
    mods=[]
    stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"Raw107REKid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck 201 (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter({"cycle":6990,"last":1217,"open":258,"split":368}),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck 201 (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split 8 (4,false) kids
theorem tree_checked : zipCheck 201 p107re tree = true := by
  change (zipQueryOK 201 p107re 8 (4,false) && allMoves (fun mv => zipCheck 201 (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate 201 p107re 6 :=
  certifiedZip 201 p107re tree p107re_root p107re_nohalt tree_checked
theorem all_completions : ∀ m, compatible p107re m → WeightedBound 201 m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
"""
    emit("Raw107REData",mods,body)
    print(stats,"FAR",251,"pumps",7)
if __name__=="__main__": main()
