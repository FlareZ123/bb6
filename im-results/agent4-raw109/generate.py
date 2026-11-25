"""Adapted from Agent1 raw60 generator; exact raw109 B1 child audits."""
from pathlib import Path
from collections import Counter
from itertools import product
import sys, subprocess, json, hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as one
import multi
import long_epoch
sys.path.insert(0,str(ROOT.parent/"agent1-ngram"))
from emit_ngram import emit as emit_ngram

MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
SPECS=json.loads((ROOT/"specs.json").read_text())

def main(a):
    spec=SPECS[a]
    B=spec["bound"]
    n,s=spec["query"]
    PARENT=f"1RB---_1RC{a}_0RD---_1LD1RE_---1RB_------"
    pre=f"Raw109B{a}"
    ns=f"BB6.Agent4{pre}"
    target=ROOT/("generated_"+a);target.mkdir(exist_ok=True)
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()==spec["sha"]
    opens=data.decode().splitlines()
    assert len(opens)==spec["stats"]["open"]==len(set(opens))
    index={s:i for i,s in enumerate(opens)}

    pn=ns+"Pumps"
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {pn}","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for gen,inds,limit in [(one,spec["one"],2500),(multi,spec["multi"],2500)]:
        for i in inds:
            p=one.parse(opens[i]);ans=gen.candidate(p,one.concrete_events(p,limit))
            assert ans is not None,(a,i)
            code,info=gen.generate(i,p,ans)
            pumps[i]=f"{pn}.M{i}"
            pumpcode.append(code)
            print(a,i,info)
    for i,st,lim,sd,q,period in spec.get("long",[]):
        p=one.parse(opens[i]);ans=long_epoch.candidate(p,[e for e in one.concrete_events(p,lim) if e[0]>=st],sd,q,period)
        assert ans is not None,(a,i)
        code,info=one.generate(i,p,ans)
        pumps[i]=f"{pn}.M{i}"
        pumpcode.append(code)
        print(a,i,info)
    manual=[]
    for i,(mod,nspace,table) in spec.get("manual",{}).items():
        assert opens[int(i)]==table,(a,i)
        pumps[int(i)]=nspace
        if mod not in manual:manual.append(mod)
    ngids=spec.get("ngram",[])
    if ngids:
        assert not (set(ngids)&set(pumps))
        subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent1-ngram/ngram.cpp"),"-o",str(target/"ngram")],check=True)
        inp="".join(f"{i} {opens[i]}\n" for i in ngids)
        out=subprocess.run([str(target/"ngram"),"12"],input=inp,text=True,capture_output=True,check=True)
        certs=dict(l.split(maxsplit=1) for l in out.stdout.splitlines())
        assert set(map(int,certs))==set(ngids),out.stderr
        mod=pre+"NGram"
        gn=ns+"NGram"
        code=["import NGramCertificate","set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {gn}","open BB6Coverage BB6.Agent1NGram"]
        for i in ngids:
            code.extend([f"namespace M{i}",emit_ngram(i,opens[i],certs[str(i)]),
                         f"abbrev table := p{i}",
                         f"theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never{i} m hm",
                         f"end M{i}"])
            pumps[i]=f"{gn}.M{i}"
        code.append(f"end {gn}")
        (ROOT/(mod+".lean")).write_text("\n\n".join(code)+"\n")
        manual.append(mod)
    exceptions={int(i):t for i,t in spec["unresolved"].items()}
    assert all(opens[i]==t for i,t in exceptions.items())
    assert not (set(pumps)&set(exceptions))
    late={int(i):(n,s) for i,(n,s,t) in spec.get("late",{}).items() if opens[int(i)]==t and t.count("---")==1}
    assert len(late)==len(spec.get("late",{}))
    assert not (set(late)&(set(pumps)|set(exceptions)))
    extra={int(i):c for i,(t,c) in spec.get("extra_far",{}).items() if opens[int(i)]==t}
    assert len(extra)==len(spec.get("extra_far",{}))
    assert not (set(extra)&(set(pumps)|set(exceptions)|set(late)))
    far=[i for i in range(len(opens)) if i not in pumps and i not in exceptions and i not in late and i not in extra]
    subprocess.run(["g++","-std=c++20","-O3",str(ROOT.parent/"agent11-raw107/bank.cpp"),"-o",str(target/"bank")],check=True)
    inputs="".join(f"{i} {opens[i].replace('_','')}\n" for i in far)
    out=subprocess.run([str(target/"bank"),str(ROOT.parent/"agent1-raw60/bank.txt")],input=inputs,text=True,capture_output=True,check=True)
    dfa={int(i):c for i,c in (l.split() for l in out.stdout.splitlines())}
    assert set(dfa)==set(far),out.stderr
    dfa.update(extra)
    exc_names={i:f"exception{j}" for j,i in enumerate(exceptions)}
    exc_index={i:j for j,i in enumerate(exceptions)}
    exc_defs=[]
    for i,t in exceptions.items():
        transitions=t.replace("_","")
        lines=[f"def {exc_names[i]} : PartialMachine := fun s =>","  match s.1.val,s.2 with"]
        for j in range(12):
            code=transitions[3*j:3*j+3]
            if code!="---":
                lines.append(f"  | {j//2},{str(bool(j%2)).lower()} => some (some {move(code)})")
        lines.append("  | _,_ => none")
        exc_defs.append("\n".join(lines))
    exc_defs.append("def exceptionTable (i : Fin "+str(len(exceptions))+") : PartialMachine :=\n  match i.val with\n"+"\n".join(f"  | {j} => {exc_names[i]}" for i,j in exc_index.items())+"\n  | _ => fun _ => none")
    exc_defs.append("def Exceptions : Prop := ∀ i : Fin "+str(len(exceptions))+", ∀ m, compatible (exceptionTable i) m → NeverHalts m")
    exc_text="\n\n".join(exc_defs)
    pumpcode.append(f"end {pn}")
    (ROOT/(pre+"Pumps.lean")).write_text("\n\n".join(pumpcode)+"\n")
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
            nn,ss=v
            return f".last {nn} {slot(ss)}"
        if tag=="open":
            t=v[0];i=index[t]
            if i in late:
                nn,ss=late[i]
                return f".last {nn} {slot(ss)}"
            if i in pumps:return f".proven {pumps[i]}.table {pumps[i]}.never"
            if i in exceptions:return f".proven (exceptionTable ⟨{exc_index[i]},by decide⟩) (h ⟨{exc_index[i]},by decide⟩)"
            c=dfa[i];rev=int(c[0]);d,D,L,R,z=masks(parse(t),rev,[int(ch,36) for ch in c[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        nn,ss,kids=v;assert len(kids)==24
        return f".split {nn} {slot(ss)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    assert tree[:3]==["split",n,s]
    bname=pre+"Base"
    emit(bname,["ZipThreeHoleAudit",pre+"Pumps"]+manual,f"""
{exc_text}

abbrev p109 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,true,1⟩)
abbrev parent : PartialMachine := refine p109 (1,true) (some {move(a)})
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
def kid{i:02} (h : Exceptions) : Audit := {build(kid)}
theorem check{i:02} (h : Exceptions) : zipCheck {B} (child {move(MOVES[i])}) (kid{i:02} h) = true := by rfl
""")
    assert stats==Counter(spec["stats"]),stats
    cases="\n".join(f"  · exact check{12*w+6*r+q:02} h" for q,w,r in product(range(6),range(2),range(2)))
    closed="" if exceptions else f"theorem all_closed : ∀ m, compatible parent m → WeightedBound {B} m :=\n  all_completions (fun i => Fin.elim0 i)\n#print axioms all_closed\n"
    emit(pre+"Data",mods,f"""
def kids (h : Exceptions) : Move → Audit := byMove [{",".join(f"kid{i:02} h" for i in range(24))}]
theorem kids_checked (h : Exceptions) (mv : Move) : zipCheck {B} (child mv) (kids h mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def tree (h : Exceptions) : Audit := .split {n} {slot(s)} (kids h)
theorem tree_checked (h : Exceptions) : zipCheck {B} parent (tree h) = true := by
  change (zipQueryOK {B} parent {n} {slot(s)} && allMoves (fun mv => zipCheck {B} (child mv) (kids h mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query, allMoves_of _ (kids_checked h)⟩
noncomputable def certificate (h : Exceptions) : WeightedTNFCertificate {B} parent 6 :=
  certifiedZip {B} parent (tree h) parent_root parent_nohalt (tree_checked h)
theorem all_completions (h : Exceptions) : ∀ m, compatible parent m → WeightedBound {B} m :=
  (certificate h).sound
#print axioms tree_checked
#print axioms all_completions
{closed}""")
    print(stats,"FAR",len(far),"pumps",len(pumps),"exceptions",len(exceptions))

if __name__=="__main__":
    for a in sys.argv[1:] or SPECS:main(a)
