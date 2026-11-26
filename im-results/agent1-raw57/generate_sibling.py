"""Complete candidate tree for canonical Raw57, extending Agent6's sibling generator.
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
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent47-raw112-cut/enumerate_fast.cpp"),"-o",str(target/"enumerate")],check=True)
    subprocess.run([str(target/"enumerate"),PARENT],cwd=target,check=True)
    data=(target/"open.txt").read_bytes()
    assert hashlib.sha256(data).hexdigest()==SPEC["hash"]
    opens=data.decode().splitlines()
    assert len(opens)==SPEC["stats"]["open"]==len(set(opens))
    index={s:i for i,s in enumerate(opens)}
    dfa=[SPEC.get("default","")]*len(opens)
    for row in OVERRIDES.split():
        i,a=row.split(":");dfa[int(i)]=a
    pumpns=f"BB6.Agent1{ID}Pumps"
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
        pumps[int(i)]=f"BB6Coverage.Agent1{module}"
        packed=ROOT/(module+".lean.gz.b64")
        if packed.is_file():
            import gzip,base64
            (ROOT/(module+".lean")).write_bytes(gzip.decompress(base64.b64decode(packed.read_bytes().strip(),validate=True)))
        if "import "+module not in pumpcode:
            pumpcode.insert(0,"import "+module)
    if SPEC.get("ngram"):
        nroot=ROOT.parent/"agent47-raw111-cut"
        sys.path.insert(0,str(nroot))
        import emit_sparse
        exe=target/"ngram_sparse"
        subprocess.run(["g++","-std=c++17","-O3",str(nroot/"ngram_sparse.cpp"),"-o",str(exe)],check=True)
        for i,counts in SPEC["ngram"].items():
            i=int(i); k,*expected=counts
            res=subprocess.check_output([str(exe),str(k)],input=f"{i} {opens[i]}\n",text=True)
            j,data=res.strip().split(maxsplit=1);assert int(j)==i
            module,certns=emit_sparse.emit(ROOT,i,opens[i],data,width=k,expected=expected,module_name=f"{ID}Sparse{i}")
            assert i not in pumps
            pumps[i]=certns
            pumpcode.insert(0,"import "+module)
    if SPEC.get("automata") or SPEC.get("ngram_automata"):
        sys.path.insert(0,str(ROOT.parent/"agent4-raw58"))
        from generate_more import run_automata, compress_automata, emit_automata_sharded
        an=f"BB6.Agent7{ID}Automata"
        am=ID+"Automata"
        code=["import TwoSidedAutomata","set_option maxRecDepth 100000",
              "set_option maxHeartbeats 0",f"namespace {an}","open BB6Coverage"]
        for i,params in SPEC.get("automata",{}).items():
            i=int(i)
            p=one.parse(opens[i])
            L,R=(params["left"],params["right"]) if isinstance(params,dict) else (params,params)
            cert=run_automata(p,tuple(L),tuple(R))
            assert cert[0],(A,i,params)
            before=cert[1]
            cert=compress_automata(p,cert)
            print(A,i,"automata",before,"->",cert[1],flush=True)
            code.append(emit_automata_sharded(i,p,cert))
            assert i not in pumps
            pumps[i]=f"{an}.M{i}"
        if SPEC.get("ngram_automata"):
            from ngram_auto import from_sparse
            nroot=ROOT.parent/"agent47-raw111-cut"
            exe=target/"ngram_sparse_auto"
            subprocess.run(["g++","-std=c++17","-O3",str(nroot/"ngram_sparse.cpp"),"-o",str(exe)],check=True)
            for i,expected in SPEC["ngram_automata"].items():
                i=int(i); k,before,after=expected
                p=one.parse(opens[i])
                raw=subprocess.check_output([str(exe),str(k)],input=f"{i} {opens[i]}\n",text=True)
                j,data=raw.strip().split(maxsplit=1); assert int(j)==i
                cert=from_sparse(p,data); assert cert[1]==before
                cert=compress_automata(p,cert); assert cert[1]==after
                print(A,i,"ngram incidence quotient",before,"->",after,flush=True)
                code.append(emit_automata_sharded(i,p,cert))
                assert i not in pumps
                pumps[i]=f"{an}.M{i}"
        code.append(f"end {an}")
        (ROOT/(am+".lean")).write_text("\n\n".join(code)+"\n")
        pumpcode.insert(0,"import "+am)
    pumpcode.append(f"end {pumpns}")
    (ROOT/(ID+"Pumps.lean")).write_text("\n\n".join(pumpcode)+"\n")
    ns=f"BB6.Agent1{ID}"
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
    # Use the same compositional zipCheck proof pattern as raw60's
    # shard_audit.py. Restrict the new layout to our interrupted children.
    # A split is checked from its query and all 24 exact refined children;
    # leaf checks and the final full-tree census are unchanged.
    def size(node):
        return 1 + sum(map(size, node[3])) if node[0] == "split" else 1
    def emit_subtree(node, p, kn, cn, module):
        def leaf(t, pp, k, c):
            return f"def {k} : Audit := {build(t)}\ntheorem {c} : zipCheck {BOUND} ({pp}) {k} = true := by decide\n"
        if A not in ("0LB", "1RF") or size(node) <= 300 or node[0] != "split":
            emit(module, [bname], leaf(node,p,kn,cn))
            return
        stats["split"] += 1
        _, nn, ss0, children = node
        assert len(children) == 24
        sl = slot(ss0)
        ks, cs, imports, small = [], [], [], []
        chunk = 0
        def flush():
            nonlocal chunk
            if small:
                name = module + f"Chunk{chunk:02}"
                emit(name, [bname], "\n".join(small))
                imports.append(name)
                small.clear()
                chunk += 1
        for j, sub in enumerate(children):
            k, c = kn+f"_{j:02}", cn+f"_{j:02}"
            ks.append(k); cs.append(c)
            pp = f"refine ({p}) {sl} (some {move(MOVES[j])})"
            if size(sub) > 300 and sub[0] == "split":
                flush()
                name = module+f"Sub{j:02}"
                emit_subtree(sub,pp,k,c,name)
                imports.append(name)
            else:
                body0 = leaf(sub,pp,k,c)
                if sum(map(len,small))+len(body0)>10000:
                    flush()
                small.append(body0)
        flush()
        cases0="\n".join(f"  · exact {cs[12*w+6*r+q]}" for q,w,r in product(range(6),range(2),range(2)))
        emit(module,imports,f"""
def {kn}Kids : Move → Audit := byMove [{",".join(ks)}]
def {kn} : Audit := .split {nn} {sl} {kn}Kids
theorem {cn}_kids (mv : Move) : zipCheck {BOUND} (refine ({p}) {sl} (some mv)) ({kn}Kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases0}
theorem {cn} : zipCheck {BOUND} ({p}) {kn} = true := by
  change (zipQueryOK {BOUND} ({p}) {nn} {sl} && allMoves (fun mv => zipCheck {BOUND} (refine ({p}) {sl} (some mv)) ({kn}Kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ {cn}_kids⟩
""")
    mods=[]
    stats["split"]+=1
    for i,kid in enumerate(tree[3]):
        name=f"{ID}Kid{i:02}";mods.append(name)
        emit_subtree(kid,f"child {move(MOVES[i])}",f"kid{i:02}",f"check{i:02}",name)
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
