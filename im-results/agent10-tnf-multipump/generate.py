"""Build complete candidate audit trees for raw92, raw100 and raw101.

All verdicts must be checked by Lean. The fixed cap only selects leaves for
FAR or symbolic proof discovery. The open-list digest pins witness indexing.
"""
from pathlib import Path
import sys,json,hashlib,subprocess
from collections import Counter
from itertools import product
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as one
import multi
import long_epoch
SPECS=json.loads((ROOT/"specs.json").read_text())
SPECS={k:SPECS[k] for k in (sys.argv[1:] or ["92","100","101"])}
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(ROOT/"enumerate")],check=True)
for raw,spec in SPECS.items():
    target=ROOT/("raw"+raw)
    target.mkdir(exist_ok=True)
    bound=spec["bound"]
    if "b1" in spec:
        f1=spec["b1"];depth=5;parentslot="(1,true)"
        PARENT="1RB---_1RC"+f1+"_0RD---_1LD1RE_---0LB_------"
    else:
        f1=spec["f1"];depth=6;parentslot="(5,true)"
        PARENT="1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---"+f1
    subprocess.run([str(ROOT/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()==spec["hash"],raw
    opens=data.decode().splitlines()
    assert len(opens)==spec["stats"]["open"]==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=["00102030400"]*len(opens)
    for row in spec["dfa"].split():
        i,a=row.split(":");dfa[int(i)]=a
    pumps={}
    pumpns=f"BB6.Agent10Raw{raw}Pumps"
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {pumpns}","open BB6Coverage BB6Coverage.Agent31Pump"]
    for mod,key in [(one,"one"),(multi,"two")]:
        for i in spec[key]:
            p=one.parse(opens[i]);ans=mod.candidate(p,one.concrete_events(p,6000))
            assert ans is not None,(raw,i,key)
            code,info=mod.generate(i,p,ans)
            pumps[i]=f"{pumpns}.M{i}"
            pumpcode.append(code)
            print(raw,i,key,info)
    for i in spec.get("long",[]):
        p=one.parse(opens[i])
        side,state,period=spec.get("long_params",{}).get(str(i),("R",4,3) if raw=="86" else ("R",0,1))
        ans=long_epoch.candidate(p,one.concrete_events(p,10000),side,state,period)
        assert ans is not None,(raw,i,"long")
        code,info=one.generate(i,p,ans)
        pumps[i]=f"{pumpns}.M{i}"
        pumpcode.append(code)
        print(raw,i,"long",info)
    if spec.get("recursive"):
        pumpcode.insert(0,"import RecursiveGrowth")
        for i in spec["recursive"]:
            pumps[i]=f"BB6.Agent10Recursive.R{raw}M{i}"
    pumpcode.append(f"end {pumpns}")
    (ROOT/f"Raw{raw}Pumps.lean").write_text("\n\n".join(pumpcode)+"\n")
    ns=f"BB6.Agent10Raw{raw}"
    def emit(name,imports,body):
        header=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
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
            a=dfa[i];rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,list(map(int,a[1:])))
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        n,s,kids=v;assert len(kids)==24
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    n,s=spec["root"];ss=slot(s)
    assert tree[:3]==["split",n,s]
    bname=f"Raw{raw}Base"
    emit(bname,["ThreeHoleAudit",f"Raw{raw}Pumps"],f"""
abbrev p{raw} : PartialMachine :=
  refine (pathEnd root 2 (path.take {depth})).1 {parentslot} (some {move(f1)})
theorem p{raw}_root : p{raw} initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p{raw}_nohalt : weightedTNFNoAssignedHalt p{raw} :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take {depth}) firstOneCylinder_no_assigned_halt)
abbrev child{raw} (mv : Move) := refine p{raw} {ss} (some mv)
theorem query{raw} : queryOK {bound} p{raw} {n} {ss} = true := by decide
""")
    mods=[]
    for i,kid in enumerate(tree[3]):
        name=f"Raw{raw}Kid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : check {bound} (child{raw} {move(MOVES[i])}) kid{i:02} = true := by decide
""")
    assert stats==Counter(spec["stats"]),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    body=f"""
def kids{raw} : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids{raw}_checked (mv : Move) : check {bound} (child{raw} mv) (kids{raw} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree{raw} : Audit := .split {n} {ss} kids{raw}
theorem tree{raw}_checked : check {bound} p{raw} tree{raw} = true := by
  change (queryOK {bound} p{raw} {n} {ss} && allMoves (fun mv => check {bound} (child{raw} mv) (kids{raw} mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query{raw}, allMoves_of _ kids{raw}_checked⟩
noncomputable def certificate{raw} : WeightedTNFCertificate {bound} p{raw} 6 :=
  certified {bound} p{raw} tree{raw} p{raw}_root p{raw}_nohalt tree{raw}_checked
theorem all{raw} : ∀ m, compatible p{raw} m → WeightedBound {bound} m :=
  certificate{raw}.sound
#print axioms tree{raw}_checked
#print axioms all{raw}
"""
    emit(f"Raw{raw}Data",mods,body)
    print("raw",raw,stats,"FAR",len(opens)-len(pumps),"pumps",len(pumps))
