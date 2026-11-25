"""Candidate exhaustive proof for raw58, A1=0RE. All verdicts require Lean acceptance."""
from pathlib import Path
from collections import Counter
from itertools import product
import sys, subprocess, json, hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse
PARENT="1RB0RE_1RC---_0RD---_1LD1RE_---0RA_------"
BOUND=55
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
GROUPS="""00101 0,1,2,10,20,24,26,45,52,53,56,58,59,60,63,64,65,71,72,73,78,79,80,92,97,98,100,113,142,145,160,162,165,166,167,174,187,191,192,193,219,223,231,244
10123224122 4
0012101 5,62
10632727373315437 6
101213333 14,17,21,23,33,48,76,112,119,133,201,203,209,215,239
0010202 29,75,77,84,87,123,124,125,126,130,141,149,161,163,168,172,173,202,218,229,242,243
001023031 32
100 51,67,68,70,82,108,109,110,135,136,137
00123414301 61
0010201 69,81,85
00121032421 88,122
101212333 117,129
00102324201 120,159
005312464243135 121
00121312421 151,152,189,190
001023201 153
00123012423 188
10121343333 198
00100 224,225,226,227,245,247
00102342201 228"""
def main():
    target=ROOT/"generated"; target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()=="44c8da46e8c6858212f220e5309b2a0df9da196572144b7b9a663f7b444857d1"
    opens=data.decode().splitlines()
    assert len(opens)==251==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["000"]*251
    for line in GROUPS.splitlines():
        code,ids=line.split()
        for i in map(int,ids.split(",")): dfa[i]=code
    assert opens[89]=="1RB0RE_1RC---_0RD0LF_1LD1RE_1LC0RA_1LB1LE"
    ns="BB6.Agent4Raw58RE"
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
            if i==89:return ".cycle 39 278 true (-3)"
            a=dfa[i];rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,[int(ch,36) for ch in a[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        n,s,kids=v;assert len(kids)==24
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    assert tree[:3]==["split",8,8]
    bname="Raw58REBase"
    emit(bname,["ZipThreeHoleAudit"],"""
abbrev p58 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,0⟩)
abbrev p58re : PartialMachine := refine p58 (0,true) (some ⟨false,true,4⟩)
theorem p58re_root : p58re initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p58re_nohalt : weightedTNFNoAssignedHalt p58re :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine p58re (4,false) (some mv)
theorem query : zipQueryOK 55 p58re 8 (4,false) = true := by decide
""")
    mods=[]
    stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"Raw58REKid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck 55 (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter({"cycle":8715,"last":2259,"open":251,"split":488}),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck 55 (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split 8 (4,false) kids
theorem tree_checked : zipCheck 55 p58re tree = true := by
  change (zipQueryOK 55 p58re 8 (4,false) && allMoves (fun mv => zipCheck 55 (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate 55 p58re 6 :=
  certifiedZip 55 p58re tree p58re_root p58re_nohalt tree_checked
theorem all_completions : ∀ m, compatible p58re m → WeightedBound 55 m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
"""
    emit("Raw58REData",mods,body)
    print(stats,"FAR",250,"late cycle",1)
if __name__=="__main__": main()
