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
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import multi
SPECS=json.loads((ROOT/"siblings.json").read_text())
A=sys.argv[1]
SPEC=SPECS[A]
ID="Raw57"+A[1:]+A[0]
PARENT=f"1RB{A}_1RC---_0RD---_1LD1RE_---0LA_------"
BOUND=SPEC["bound"]
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
OVERRIDES=SPEC.get("dfa","")
def main():
    target=ROOT/("generated-"+A); target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()==SPEC["hash"]
    opens=data.decode().splitlines()
    assert len(opens)==SPEC["stats"]["open"]==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=[SPEC.get("default","")]*len(opens)
    for row in OVERRIDES.split():
        i,a=row.split(":");dfa[int(i)]=a
    pumpns=f"BB6.Agent6{ID}Pumps"
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {pumpns}","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for mod,key in [(one,"one"),(multi,"two")]:
        for i in SPEC[key]:
            p=one.parse(opens[i]);ans=mod.candidate(p,one.concrete_events(p,6000))
            assert ans is not None,(A,i)
            code,info=mod.generate(i,p,ans)
            pumps[i]=f"{pumpns}.M{i}"
            pumpcode.append(code)
            print(A,i,info)
    for i,module in SPEC.get("extra",{}).items():
        pumps[int(i)]=f"{pumpns}.M{i}"
        pumpcode.insert(0,"import "+module)
    pumpcode.append(f"end {pumpns}")
    (ROOT/(ID+"Pumps.lean")).write_text("\n\n".join(pumpcode)+"\n")
    ns=f"BB6.Agent6{ID}"
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
            candidates=SPEC["bank"].split() if "bank" in SPEC else [dfa[i]]
            for a in candidates:
                rev=int(a[0])
                try:
                    d,D,L,R,z=masks(parse(code),rev,[int(ch,36) for ch in a[1:]])
                except AssertionError:
                    continue
                break
            else: raise AssertionError((A,i,code,"no FAR witness"))
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        n,s,kids=v;assert len(kids)==24
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    n,s=SPEC["root"][1:];ss=slot(s)
    assert tree[:3]==SPEC["root"]
    bname=ID+"Base"
    emit(bname,["ZipThreeHoleAudit",ID+"Pumps"],f"""
abbrev p57 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,0⟩)
abbrev p57ra : PartialMachine := refine p57 (0,true) (some {move(A)})
theorem p57ra_root : p57ra initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p57ra_nohalt : weightedTNFNoAssignedHalt p57ra :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine p57ra {ss} (some mv)
theorem query : zipQueryOK {BOUND} p57ra {n} {ss} = true := by decide
""")
    mods=[]
    stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"{ID}Kid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck {BOUND} (child {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter(SPEC["stats"]),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck {BOUND} (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split {n} {ss} kids
theorem tree_checked : zipCheck {BOUND} p57ra tree = true := by
  change (zipQueryOK {BOUND} p57ra {n} {ss} && allMoves (fun mv => zipCheck {BOUND} (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate {BOUND} p57ra 6 :=
  certifiedZip {BOUND} p57ra tree p57ra_root p57ra_nohalt tree_checked
theorem all_completions : ∀ m, compatible p57ra m → WeightedBound {BOUND} m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
"""
    emit(ID+"Data",mods,body)
    print(A,stats,"FAR",len(opens)-len(pumps),"pumps",len(pumps))
if __name__=="__main__": main()
