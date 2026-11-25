"""Generate source-audited raw58 child certificates; optionally discover FAR and pump covers."""
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
sys.path.insert(0,str(ROOT.parent/"agent1-ngram"))
from emit_ngram import emit as emit_ngram
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
SPECS=json.loads((ROOT/"more.json").read_text())
FAR_CODES=sorted({"000"} | {line.split()[0] for spec in SPECS.values() for line in spec.get("groups","").splitlines() if line.strip()}, key=lambda s:(len(s),s))

def main():
    for key in sys.argv[1:] or ["RD","LC1","RE1"]:
        build_child(key,SPECS[key])

def build_child(key,spec):
    target=ROOT/("generated_"+key); target.mkdir(exist_ok=True)
    parent="1RB"+spec["a1"]+"_1RC---_0RD---_1LD1RE_---0RA_------"
    bound=spec["bound"]; n=spec["query"]; ss=slot(spec.get("slot",8))
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent2-tnf-raw99/enumerate.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),parent],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    digest=hashlib.sha256(data).hexdigest()
    if "hash" in spec: assert digest==spec["hash"],(key,digest)
    else: print(key,"open_sha256",digest)
    opens=data.decode().splitlines()
    assert len(opens)==len(set(opens))
    if "stats" in spec: assert len(opens)==spec["stats"]["open"],(key,len(opens),spec["stats"]["open"])
    index={s:i for i,s in enumerate(opens)}
    dfa=["000"]*len(opens)
    assigned=set()
    for line in spec.get("groups","").splitlines():
        if not line.strip(): continue
        code,ids=line.split()
        for i in map(int,ids.split(",")): dfa[i]=code; assigned.add(i)
    auto_pumps={}; auto_multi={}
    if spec.get("auto_classify"):
        pump_ids=set(spec.get("pumps",[])); multi_ids=set(spec.get("multi",[]))
        custom_ids={int(i) for i in spec.get("custom",{})}
        unresolved=[]
        for i,p in enumerate(opens):
            if i in assigned or i in pump_ids or i in multi_ids or i in custom_ids: continue
            found=False
            for code in FAR_CODES:
                try: masks(parse(p),int(code[0]),[int(ch,36) for ch in code[1:]])
                except (AssertionError,ValueError,IndexError): continue
                dfa[i]=code; assigned.add(i); found=True; break
            if found: continue
            pp=one.parse(p); events=one.concrete_events(pp,10000)
            ans=one.candidate(pp,events)
            if ans is not None:
                spec.setdefault("pumps",[]).append(i); auto_pumps[i]=ans; continue
            ans=multi.candidate(pp,events)
            if ans is not None:
                spec.setdefault("multi",[]).append(i); auto_multi[i]=ans; continue
            unresolved.append((i,p))
        print(key,"auto FAR",len(assigned),"auto one-block",len(auto_pumps),"auto multi",len(auto_multi),"unresolved",len(unresolved))
        if unresolved:
            print("UNRESOLVED",*["%d %s"%(i,p) for i,p in unresolved[:50]],sep="\n")
            raise SystemExit(3)
    ns="BB6.Agent4Raw58"+key
    prefix="Raw58"+key
    pumpns="BB6Coverage.Agent4Raw58"+key+"Pumps"
    pumpcode=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {pumpns}","open BB6Coverage BB6Coverage.Agent31Pump"]
    pumps={}
    for i in spec.get("pumps",[]):
        p=one.parse(opens[i]); ans=auto_pumps[i] if i in auto_pumps else one.candidate(p,one.concrete_events(p,10000))
        assert ans is not None,(key,i,opens[i])
        code,info=one.generate(i,p,ans)
        pumpcode.append(code);pumps[i]=f"{pumpns}.M{i}"
        print(key,i,info)
    for i in spec.get("multi",[]):
        p=one.parse(opens[i]); ans=auto_multi[i] if i in auto_multi else multi.candidate(p,one.concrete_events(p,10000))
        assert ans is not None,(key,i,opens[i])
        code,info=multi.generate(i,p,ans)
        pumpcode.append(code);pumps[i]=f"{pumpns}.M{i}"
        print(key,i,info)
    if "primitive" in spec:
        i=spec["primitive"];p=one.parse(opens[i])
        st=one.C(1,0,0,one.W(),one.W("011","01111","011"))
        tg=one.C(1,-7,0,one.W(),one.W("011"+"01111"*3,"01111","011"))
        ans=one.pump(p,st,tg,3000)
        assert ans is not None,(key,i,opens[i])
        code,(t,a,b)=one.generate(i,p,(17,None,st,tg,ans))
        code=code.replace("some (family (n+1))","some (family (n+3))")
        code=code.replace(f"never_of_growth table family {t} (fun n => {a}+{b}*n) entry (by intro n; omega) growth m hm", f"never_of_growth table (fun n => family (3*n)) {t} (fun n => {a}+{b}*(3*n)) entry (by intro n; omega) (by intro n; simpa only [show 3*(n+1)=3*n+3 by omega] using growth (3*n)) m hm")
        pumpcode.append(code);pumps[i]=f"{pumpns}.M{i}"
    if "multiseed" in spec:
        i=spec["multiseed"];p=one.parse(opens[i])
        A,B="01111111","011011"
        st=multi.C(2,(),multi.clean(multi.lit("101011"+A)+multi.rep(A)+multi.lit(B)+multi.rep(B)))
        tg=multi.C(2,(),multi.clean(multi.lit("101011"+A*2)+multi.rep(A)+multi.lit(B*2)+multi.rep(B)))
        ans=multi.pump(p,st,tg,3000)
        assert ans is not None,(key,i,opens[i])
        code,info=multi.generate(i,p,(228,st,tg,ans))
        pumpcode.append(code);pumps[i]=f"{pumpns}.M{i}"
    ngids=spec.get("ngram",[])
    ngmod=prefix+"NGram"
    if ngids:
        subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent1-ngram/ngram.cpp"),"-o",str(target/"ngram")],check=True)
        inp="".join(f"{i} {opens[i]}\n" for i in ngids)
        out=subprocess.run([str(target/"ngram"),"12"],input=inp,text=True,capture_output=True,check=True)
        certs=dict(l.split(maxsplit=1) for l in out.stdout.splitlines())
        assert set(map(int,certs))==set(ngids),out.stderr
        gn=ns+"NGram"
        code=["import NGramCertificate","set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {gn}","open BB6Coverage BB6.Agent1NGram"]
        for i in ngids:
            code.extend([f"namespace M{i}",emit_ngram(i,opens[i],certs[str(i)]),
                         f"abbrev table := p{i}",
                         f"theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never{i} m hm",
                         f"end M{i}"])
            pumps[i]=f"{gn}.M{i}"
        code.append(f"end {gn}")
        (ROOT/(ngmod+".lean")).write_text("\n\n".join(code)+"\n")
    late={int(i):(n,s) for i,(n,s,t) in spec.get("late",{}).items() if opens[int(i)]==t and t.count("---")==1}
    assert len(late)==len(spec.get("late",{}))
    pumpcode.append(f"end {pumpns}")
    (ROOT/(prefix+"Pumps.lean")).write_text("\n\n".join(pumpcode)+"\n")
    imports=["ZipThreeHoleAudit",prefix+"Pumps"]+spec.get("imports",[])
    if ngids: imports.append(ngmod)
    for i,module in spec.get("custom",{}).items(): pumps[int(i)]=module
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
    if spec.get("explicit_partition"):
        assert not (assigned & set(pumps) or assigned & set(late) or set(pumps) & set(late))
        assert assigned | set(pumps) | set(late) == set(range(len(opens)))
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
            if i in late:
                nn,ss=late[i]
                return f".last {nn} {slot(ss)}"
            if i in pumps:return f".proven {pumps[i]}.table {pumps[i]}.never"
            a=dfa[i];rev=int(a[0]);d,D,L,R,z=masks(parse(code),rev,[int(ch,36) for ch in a[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag=="split"
        m,s,kids=v;assert len(kids)==24
        return f".split {m} {slot(s)} (byMove [\n"+",\n".join(build(k) for k in kids)+"])"
    assert tree[:3]==["split",n,spec.get("slot",8)]
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
    if "stats" in spec: assert stats==Counter(spec["stats"]),(key,stats,spec["stats"])
    else: print(key,"tree_stats",dict(stats))
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
    print(key,stats,"FAR",len(opens)-len(pumps)-len(late),"proof leaves",len(pumps),"late",len(late))
if __name__=="__main__": main()
