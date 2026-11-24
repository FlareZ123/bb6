"""Complete candidate tree for canonical raw57, A1=0RA.
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
PARENT="1RB0RA_1RC---_0RD---_1LD1RE_---0LA_------"
BOUND=273
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
OVERRIDES="8:1053522222214 16:00102344444 18:00102344444 22:00100 25:1053522222214 82:101230123 83:00123412121 100:0010202 105:1053522222214 106:1053522222214 109:10123444144 129:1053522222214 130:1053522222214 131:00120343120 133:1053522222214 136:1053522222214 144:00120343120 145:00102344444 146:0010202 147:1053522222214 148:00120343120 149:1053522222214 150:00123412121 152:1053522222214 153:102936288873851947339 156:00100 173:00123420144 176:1053522222214 178:00102344444 183:102936288873851947339"
def main():
    target=ROOT/"generated"; target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()=="dc7744b021426f3ca9d0e626529fadb99b514bef473406ee3a933ecf29da508d"
    opens=data.decode().splitlines()
    assert len(opens)==190==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["00101"]*190
    for row in OVERRIDES.split():
        i,a=row.split(":");dfa[int(i)]=a
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false","namespace BB6.Agent6Raw57RAPumps","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for i in [0,27,113,143]:
        p=one.parse(opens[i]);ans=one.candidate(p,one.concrete_events(p,6000))
        assert ans is not None
        code,info=one.generate(i,p,ans)
        pumps[i]=f"BB6.Agent6Raw57RAPumps.M{i}"
        pumpcode.append(code)
        print(i,info)
    pumps[28]="BB6.Agent6Raw57RAPumps.M28"
    assert opens[28]=="1RB0RA_1RC0LF_0RD1RB_1LD1RE_---0LA_1LC1LF"
    pumpcode.append("end BB6.Agent6Raw57RAPumps")
    (ROOT/"Raw57RAPumps.lean").write_text("\n\n".join(pumpcode)+"\n")
    ns="BB6.Agent6Raw57RA"
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
    assert tree[:3]==["split",9,3]
    bname="Raw57RABase"
    emit(bname,["ZipThreeHoleAudit","Raw57RAPumps","Raw57Counter"],"""
abbrev p57 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,0⟩)
abbrev p57ra : PartialMachine := refine p57 (0,true) (some ⟨false,true,0⟩)
theorem p57ra_root : p57ra initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p57ra_nohalt : weightedTNFNoAssignedHalt p57ra :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine p57ra (1,true) (some mv)
theorem query : zipQueryOK 273 p57ra 9 (1,true) = true := by decide
""")
    mods=[]
    stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"Raw57RAKid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck 273 (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter({"cycle":16812,"last":4205,"open":190,"split":922}),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck 273 (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split 9 (1,true) kids
theorem tree_checked : zipCheck 273 p57ra tree = true := by
  change (zipQueryOK 273 p57ra 9 (1,true) && allMoves (fun mv => zipCheck 273 (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate 273 p57ra 6 :=
  certifiedZip 273 p57ra tree p57ra_root p57ra_nohalt tree_checked
theorem all_completions : ∀ m, compatible p57ra m → WeightedBound 273 m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
"""
    emit("Raw57RAData",mods,body)
    print(stats,"FAR",185,"pumps",5)
if __name__=="__main__": main()
