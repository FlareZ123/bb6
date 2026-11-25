"""Generate source-audited raw58 child certificates; optionally discover FAR and pump covers."""
from pathlib import Path
from collections import Counter
from itertools import product
import sys, subprocess, json, hashlib, os

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as one
sys.path.insert(0,str(ROOT.parent/"agent10-tnf-multipump"))
import multi
sys.path.insert(0,str(ROOT.parent/"agent1-ngram"))
from emit_ngram import emit as emit_ngram
sys.path.insert(0,str(ROOT.parent/"agent4-two-sided-automata"))
from emit_automata import emit as emit_automata, run as run_automata
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
from emit_sparse import emit as emit_sparse
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
        automata_ids={int(i) for i in spec.get("automata",{})}
        ngram_ids=set(spec.get("ngram",[]))
        multi_seed_ids={int(i) for i in spec.get("multi_seeds",{})}
        late_ids={int(i) for i in spec.get("late",{})}
        special_ids={int(spec[k]) for k in ("primitive","multiseed","counter") if k in spec}
        unresolved=[]
        for i,p in enumerate(opens):
            if i in (assigned | pump_ids | multi_ids | custom_ids | automata_ids |
                     ngram_ids | multi_seed_ids | late_ids | special_ids): continue
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
        print(key,"auto FAR",len(assigned),"auto one-block",len(auto_pumps),
              "auto multi",len(auto_multi),"pre-sparse unresolved",len(unresolved))
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
    for idx,seed in spec.get("multi_seeds",{}).items():
        i=int(idx);t,q,l,r,tl,tr,a,b=seed
        p=one.parse(opens[i])
        pack=lambda xs:tuple(tuple(x) for x in xs)
        st=multi.C(q,pack(l),pack(r));tg=multi.C(q,pack(tl),pack(tr))
        ans=multi.pump(p,st,tg,3000)
        assert ans is not None,(key,i,opens[i])
        code,info=multi.generate(i,p,(t,st,tg,ans))
        assert info==(t,a,b),(key,i,info)
        pumpcode.append(code);pumps[i]=f"{pumpns}.M{i}"
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
    autmod=prefix+"Automata"
    autids=spec.get("automata",{})
    if autids:
        an=ns+"Automata"
        code=["import TwoSidedAutomata","set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {an}","open BB6Coverage"]
        for idx,params in autids.items():
            i=int(idx)
            p=tuple(opens[i].replace("_","")[k:k+3] for k in range(0,36,3))
            if isinstance(params,dict):
                paramsL=tuple(params["left"]); paramsR=tuple(params["right"])
            else:
                paramsL=paramsR=params
            cert=run_automata(p,paramsL,paramsR)
            assert cert[0],(key,i,params)
            code.append(emit_automata(i,p,cert));pumps[i]=f"{an}.M{i}"
        code.append(f"end {an}")
        (ROOT/(autmod+".lean")).write_text("\n\n".join(code)+"\n")
    late={int(i):(n,s) for i,(n,s,t) in spec.get("late",{}).items() if opens[int(i)]==t and t.count("---")==1}
    assert len(late)==len(spec.get("late",{}))
    pumpcode.append(f"end {pumpns}")
    (ROOT/(prefix+"Pumps.lean")).write_text("\n\n".join(pumpcode)+"\n")
    imports=["ZipThreeHoleAudit",prefix+"Pumps"]+spec.get("imports",[])
    if ngids: imports.append(ngmod)
    if autids: imports.append(autmod)
    for i,module in spec.get("custom",{}).items(): pumps[int(i)]=module
    if "counter" in spec:
        i=spec["counter"]
        assert opens[i]=="1RB0RD_1RC---_0RD0LC_1LD1RE_1RF0RA_1LC1RE"
        pumps[i]="BB6Coverage.Agent4Raw58RD1892"
        imports.append("Raw58RD1892")
    # Search remaining unclassified leaves for exact sparse width-23 n-gram invariants.
    sparse_modules=[]
    unclassified=sorted(set(range(len(opens))) - assigned - set(pumps) - set(late))
    if unclassified and len(unclassified) <= 64:
        sparse_exe=ROOT/"ngram_sparse"
        if not sparse_exe.exists():
            subprocess.run(["g++","-O3","-std=c++17",
                str(ROOT.parent/"agent47-raw111-cut/ngram_sparse.cpp"),
                "-o",str(sparse_exe)],check=True)
        for width in (23,25,27,29):
            if not unclassified: break
            remaining=[]
            for i in unclassified:
                try:
                    proc=subprocess.run([str(sparse_exe),str(width)],
                        input=f"{i} {opens[i]}\n",text=True,capture_output=True,
                        check=True,timeout=90)
                    fields=proc.stdout.strip().split(maxsplit=1)
                    if len(fields)!=2: raise ValueError("missing sparse certificate output")
                    data=fields[1]
                    k,n,L,R,_=data.split()
                    def edge_count(raw):
                        return sum(int(v).bit_count() for item in raw.rstrip(",").split(",")
                                   if item for _,v in [item.split(":")])
                    expected=(int(n),edge_count(L),edge_count(R))
                    module_name=(f"Raw58{key}Sparse{i}" if width==23
                                 else f"Raw58{key}Sparse{width}_{i}")
                    module,ns_sparse=emit_sparse(ROOT,i,opens[i],data,width=width,
                        module_name=module_name,expected=expected)
                    pumps[i]=ns_sparse
                    sparse_modules.append(module)
                    print(key,"sparse width-"+str(width),i,"states",n,
                          "edges",expected[1:],flush=True)
                except (subprocess.CalledProcessError,subprocess.TimeoutExpired,ValueError):
                    remaining.append(i)
            unclassified=remaining
    if sparse_modules:
        imports.extend(sparse_modules)
    print(key,"sparse certificates",len(sparse_modules),"remaining",len(unclassified))
    rle_modules=[]
    rle_found={}
    if unclassified and os.environ.get("RAW58_RLE_SEARCH") == "1":
        preferred=[(2,3,2),(2,2,3),(4,2,3),(4,2,2),(4,3,2),
                    (7,5,2),(7,6,1),(2,2,2),(5,3,2)]
        params_grid=preferred+[(n,c,m) for n in range(1,9)
            for c in range(1,9) for m in range(1,7)
            if (n,c,m) not in preferred]
        asym_grid=preferred+[(2,1,1),(2,1,2),(2,1,3),(2,1,4),
            (4,1,1),(4,1,2),(4,1,3),(4,1,4),(6,1,2),(6,1,3),
            (8,1,2),(8,1,3),(2,4,4),(2,5,4),(4,4,4),(4,5,4),
            (6,3,4),(6,4,4),(8,3,4),(8,4,4)]
        rle_ns=ns+"RLEExtra"; rle_mod=prefix+"RLEExtra"
        rle_code=["import TwoSidedAutomata","set_option maxRecDepth 100000",
                  "set_option maxHeartbeats 0",f"namespace {rle_ns}","open BB6Coverage"]
        remaining=[]
        for i in unclassified:
            p=tuple(opens[i].replace("_","")[k:k+3] for k in range(0,36,3))
            found=None; cert=None
            for params in params_grid:
                candidate=run_automata(p,params,params,limit=30000)
                if candidate[0]:
                    found=(params,params); cert=candidate; break
            if found is None:
                for paramsL in asym_grid:
                    for paramsR in asym_grid:
                        if paramsL==paramsR: continue
                        candidate=run_automata(p,paramsL,paramsR,limit=12000)
                        if candidate[0]:
                            found=(paramsL,paramsR); cert=candidate; break
                    if found is not None: break
            if found is None:
                remaining.append(i)
            else:
                rle_found[i]={"left":list(found[0]),"right":list(found[1])}
                rle_code.append(emit_automata(i,p,cert))
                pumps[i]=f"{rle_ns}.M{i}"
                print(key,"RLE_FOUND",i,found[0],found[1],"states",cert[1],flush=True)
        if rle_found:
            rle_code.append(f"end {rle_ns}")
            (ROOT/(rle_mod+".lean")).write_text("\n\n".join(rle_code)+"\n")
            imports.append(rle_mod)
        unclassified=remaining
        if rle_found:
            print(key,"RLE_DISCOVERED",json.dumps(rle_found,sort_keys=True),flush=True)
    if unclassified:
        if os.environ.get("RAW58_DIAG") == "1":
            def brief(w):
                return (len(w.pre),w.pre[:12],w.pre[-12:],len(w.block),
                        w.block[:12],len(w.suf),w.suf[:12],w.suf[-12:])
            for i in unclassified:
                p=one.parse(opens[i]); c=one.C(0,0,0,one.W(),one.W())
                lo=hi=0; events=[]; limit=250000
                for t in range(limit):
                    if c.h0<lo or c.h0>hi:
                        side="L" if c.h0<lo else "R"
                        lo,hi=min(lo,c.h0),max(hi,c.h0)
                        events.append((t,side,c.q,c.h0,brief(c.l),brief(c.r)))
                        if len(events)>8: events.pop(0)
                    try:
                        c=one.step(p,c)
                    except ValueError:
                        print(key,"DIAG",i,"first-hole-step",t,
                              "slot",slot(2*c.q+int(c.l.head())),
                              "state",c.q,"head",c.h0,"left",brief(c.l),
                              "right",brief(c.r),"events-tail",events,flush=True)
                        break
                else:
                    print(key,"DIAG",i,"no-hole-through",limit,
                          "state",c.q,"head",c.h0,"left",brief(c.l),
                          "right",brief(c.r),"events-tail",events,flush=True)
        print(key,"UNRESOLVED",*[f"{i} {opens[i]}" for i in unclassified],sep="\n")
        raise SystemExit(3)
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
