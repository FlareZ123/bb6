"""Generate auditable raw108 child trees from exact candidate census.

All FAR masks and leaf simulations are checked by existing Lean proof.
The open.txt digest prevents positional witness mismatches.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import sys, subprocess, json, hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse

MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
SPECS=json.loads((ROOT/"specs.json").read_text())
import build_lb
SPECS["0LB"]=build_lb.load()

def main(a):
    spec=SPECS[a]
    B=spec["bound"]
    n,s=spec["query"]
    PARENT=f"1RB---_1RC{a}_0RD---_1LD1RE_---1LB_------"
    pre=f"Raw108B{a}"
    ns=f"BB6.Agent10{pre}"
    target=ROOT/("generated_"+a);target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()==spec["sha"]
    opens=data.decode().splitlines()
    assert len(opens)==spec["stats"]["open"]==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    witnesses={}
    for row in spec.get("groups","").splitlines():
        c,ids=row.split()
        for i in ids.split(","):
            i=int(i); assert i not in witnesses
            witnesses[i]=("far",c)
    manual=[]
    if spec.get("auto"):
        sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
        import multi
        aname=f"Raw108Auto{a}"
        nsa=f"BB6.Agent10{aname}"
        parts=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
               f"namespace {nsa}","open BB6Coverage BB6Coverage.Agent31Pump"]
        def cv(w):return tuple((s,b) for s,b in w)
        for i,(t,q,l,r,L,R) in spec["auto"].items():
            i=int(i);assert i not in witnesses
            st=multi.C(q,cv(l),cv(r));tg=multi.C(q,cv(L),cv(R))
            p=multi.parse(opens[i])
            ans=multi.pump(p,st,tg,limit=spec.get("pump_limit",500))
            assert ans is not None,(a,i)
            code,info=multi.generate(i,p,(t,st,tg,ans))
            parts.append(code);witnesses[i]=("proven",f"{nsa}.M{i}")
        parts.append(f"end {nsa}")
        (ROOT/(aname+".lean")).write_text("\n\n".join(parts)+"\n")
        manual.append(aname)
    if spec.get("grammar115"):
        import grammar115
        grammar115.main()
    if spec.get("grammar854"):
        import grammar854
        grammar854.main()
    if spec.get("countergen"):
        import countergen
        countergen.main()
    if spec.get("phase_sections"):
        import phase_sections
        for i,desc in spec["phase_sections"].items():
            mod,nspace,table=spec["manual"][i]
            assert desc["table"]==table
            phase_sections.emit(desc,mod,nspace)
    if spec.get("phase_chain"):
        import phase_chain
        for i,desc in spec["phase_chain"].items():
            mod,nspace,table=spec["manual"][i]
            assert desc["table"]==table
            phase_chain.emit(desc,mod,nspace)
    if a=="0LB":
        build_lb.prepare(spec,opens,target,witnesses,manual,slot)
        import generate_long_trace
        generate_long_trace.generate(ROOT)
    if spec.get("block"):
        import block_witness
        for i,params in spec["block"].items():
            mod,nspace,table=spec["manual"][i]
            assert opens[int(i)]==table
            block_witness.emit(mod,nspace,table,params)
    for i,(mod,nspace,table) in spec.get("manual",{}).items():
        i=int(i);assert opens[i]==table and i not in witnesses
        witnesses[i]=("proven",nspace)
        if mod not in manual:manual.append(mod)
    for i,cyc in spec.get("long_cycles",{}).items():
        i=int(i);assert i not in witnesses
        witnesses[i]=("cycle",cyc)
    for i,(nn,ss) in spec.get("late",{}).items():
        i=int(i);assert i not in witnesses
        p=parse(opens[i])
        assert sum(x=="---" for x in p)==1 and p[ss]=="---",(a,i,p,ss)
        witnesses[i]=("late",(nn,ss))
    farcache={}
    for i,t in enumerate(opens):
        if i in witnesses:continue
        for c in spec.get("bank",[]):
            try:
                m=masks(parse(t),int(c[0]),[int(ch,36) for ch in c[1:]])
            except AssertionError:
                continue
            witnesses[i]=("far",c);farcache[i]=m;break
    assert set(witnesses)==set(range(len(opens))), sorted(set(range(len(opens)))-set(witnesses))
    def emit(name,imports,body):
        header=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole {'BB6.Agent10Raw108FastAudit' if a=='0LB' else 'BB6.Agent10ZipAudit'}
"""
        (ROOT/(name+".lean")).write_text("".join("import "+i+"\n" for i in imports)+header+body+f"\nend {ns}\n")
    tree=json.loads((target/"tree.json").read_text());stats=Counter()
    def cycle(e,k,r,b):
        return f".cycle {e} {k} {str(bool(r)).lower()} ({b})"
    def build(node):
        tag,*v=node;stats[tag]+=1
        if tag=="cycle":return cycle(*v)
        if tag=="last":
            nn,ss=v;return f".last {nn} {slot(ss)}"
        if tag=="open":
            t=v[0];i=index[t];kind,val=witnesses[i]
            if kind=="subtree":return val
            if kind=="proven":return f".proven {val}.table {val}.never"
            if kind=="cycle":return cycle(*val)
            if kind=="late":return f".last {val[0]} {slot(val[1])}"
            c=val;rev=int(c[0]);d,D,L,R,z=farcache[i] if i in farcache else masks(parse(t),rev,[int(ch,36) for ch in c[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        nn,ss,kids=v;assert len(kids)==24
        return f".split {nn} {slot(ss)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    assert tree[:3]==["split",n,s]
    bname=pre+"Base"
    emit(bname,["Raw108LongAudit" if a=="0LB" else "ZipThreeHoleAudit"]+manual,f"""
abbrev p108 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,1⟩)
abbrev parent : PartialMachine := refine p108 (1,true) (some {move(a)})
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
abbrev child (mv : Move) := refine parent {slot(s)} (some mv)
theorem query : zipQueryOK {B} parent {n} {slot(s)} = true := by decide
""")
    mods=[];stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"{pre}Kid{i:02}";mods.append(name)
        emit(name,[bname],f"""
def kid{i:02} : Audit := {build(kid)}
theorem check{i:02} : zipCheck {B} (child {move(MOVES[i])}) kid{i:02} = true := by rfl
""")
    assert stats==Counter(spec["stats"]),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
    emit(pre+"Data",mods,f"""
def kids : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]
theorem kids_checked (mv : Move) : zipCheck {B} (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree : Audit := .split {n} {slot(s)} kids
theorem tree_checked : zipCheck {B} parent tree = true := by
  change (zipQueryOK {B} parent {n} {slot(s)} && allMoves (fun mv => zipCheck {B} (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedZip {B} parent tree parent_root parent_nohalt tree_checked
theorem all_completions : ∀ m, compatible parent m → WeightedBound {B} m :=
  certificate.sound
#print axioms tree_checked
#print axioms all_completions
""")
    print(stats,Counter(v[0] for v in witnesses.values()))

if __name__=="__main__":
    for a in sys.argv[1:] or SPECS:main(a)
