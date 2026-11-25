"""Produce complete source-audit candidates for raw58 children 0RD, 1LC, 1RE."""
from pathlib import Path
from collections import Counter
from itertools import product
import sys, subprocess, json, hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as one
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
SPECS=json.loads((ROOT/"more.json").read_text())

def main():
    for key in sys.argv[1:] or list(SPECS):
        build_child(key,SPECS[key])

def build_child(key,spec):
    target=ROOT/("generated_"+key); target.mkdir(exist_ok=True)
    parent="1RB"+spec["a1"]+"_1RC---_0RD---_1LD1RE_---0RA_------"
    bound=spec["bound"]; n=spec["query"]; ss="(4,false)"
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),parent],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()==spec["hash"]
    opens=data.decode().splitlines()
    assert len(opens)==spec["stats"]["open"]==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["000"]*len(opens)
    for line in spec["groups"].splitlines():
        code,ids=line.split()
        for i in map(int,ids.split(",")): dfa[i]=code
    ns="BB6.Agent4Raw58"+key
    prefix="Raw58"+key
    pumpns="BB6Coverage.Agent4Raw58"+key+"Pumps"
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {pumpns}","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for i in spec["pumps"]:
        p=one.parse(opens[i]); ans=one.candidate(p,one.concrete_events(p,10000))
        assert ans is not None,(key,i,opens[i])
        code,info=one.generate(i,p,ans)
        pumpcode.append(code);pumps[i]=f"{pumpns}.M{i}"
        print(key,i,info)
    pumpcode.append(f"end {pumpns}")
    (ROOT/(prefix+"Pumps.lean")).write_text("\n\n".join(pumpcode)+"\n")
    imports=["ZipThreeHoleAudit",prefix+"Pumps"]
    if "counter" in spec:
        i=spec["counter"]
        assert opens[i]=="1RB0RD_1RC---_0RD0LC_1LD1RE_1RF0RA_1LC1RE"
        pumps[i]="BB6Coverage.Agent4Raw58RD1892"
        imports.append("Raw58RD1892")
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
            m,s=v
            return f".last {m} {slot(s)}"
        if tag=="open":
            code=v[0];i=index[code]
            if i in pumps:return f".proven {pumps[i]}.table {pumps[i]}.never"
            a=dfa[i];rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,[int(ch,36) for ch in a[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        m,s,kids=v;assert len(kids)==24
        return f".split {m} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    assert tree[:3]==["split",n,8]
    bname=prefix+"Base"
    emit(bname,imports,f"""
abbrev p58 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,0⟩)
abbrev parent : PartialMachine := refine p58 (0,true) (some {move(spec["a1"])})
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine parent {ss} (some mv)
theorem query : zipQueryOK {bound} parent {n} {ss} = true := by decide
""")
    mods=[];stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"{prefix}Kid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck {bound} (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter(spec["stats"]),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck {bound} (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split {n} {ss} kids
theorem tree_checked : zipCheck {bound} parent tree = true := by
  change (zipQueryOK {bound} parent {n} {ss} && allMoves (fun mv => zipCheck {bound} (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate {bound} parent 6 :=
  certifiedZip {bound} parent tree parent_root parent_nohalt tree_checked
theorem all_completions : ∀ m, compatible parent m → WeightedBound {bound} m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
"""
    emit(prefix+"Data",mods,body)
    print(key,stats,"FAR",len(opens)-len(pumps),"proof leaves",len(pumps))
if __name__=="__main__": main()
