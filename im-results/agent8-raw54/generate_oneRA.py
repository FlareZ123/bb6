"""Generate the complete exact-threshold proof for the Raw54 E0=1RA child."""
from collections import Counter
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile, sys
from generate_rf_witnesses import ROOT, masks, parse
from generate_ra import Node, zrun, table, refine, all_moves, slot, move, MOVES, fuse_sparse
from generate_rf_run_quotients import run_search, edge_count
from emit_mask import emit_data, emit as emit_mask
from quotient_search import search as search_sparse
from generate_oneRA_counter import emit as emit_counter
from generate_oneRA_growth import emit as emit_growth
from generate_oneRA_late import emit as emit_late
from generate_oneRA_pair import emit as emit_pair
from generate_augmented_runs import emit as emit_aug
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
from emit_sparse import emit
PARENT="1RB---_1RC---_0RD---_1LD0LE_1RA0LE_------"
BOUND=39447
NS="BB6.Agent8Raw54.OneRA"
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent8Raw54.OneRA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
"""
def write(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join("import "+m+"\n" for m in sorted(set(imports)))+HEADER+body+"\nend "+NS+"\n")

def emit_tree(node,p,expr,name,t,threshold):
    mod="Raw54OneRAShard"+name.removeprefix("oneRAShard").replace("_","X")
    imports={"Raw54OneRABase"}
    body=[]
    def local(n,c,p2,e2,prefix):
        imports.update(c.deps)
        if c.tag=="open" and c.text==".last 39446 (0,true)":
            imports.add("Raw54OneRALate")
            body.extend([
                f"def {n} : Audit := {c.term()}",
                f"theorem {n}_checked : zipCheck {BOUND} ({e2}) {n} = true := by",
                f"  have h : ({e2}) = BB6.Agent8Raw54.OneRALate.M39447.table := tableOK_sound _ _ (by decide)",
                f"  rw [h]",
                f"  exact BB6.Agent8Raw54.OneRALate.M39447.checked"])
            return
        body.extend([
            f"def {n} : Audit := {c.term()}",
            f"def {n}Table : PartialMachine := {table(p2)}",
            f"theorem {n}Table_eq : {n}Table = ({e2}) := tableOK_sound _ _ (by decide)",
            f"def {n}Prefix : Z := {zrun(p2,prefix)}",
            f"theorem {n}_checked : zipCheck {BOUND} ({e2}) {n} = true := by",
            f"  rw [← {n}Table_eq, ← checkAt_eq {BOUND} {n}Table {n} {prefix} {n}Prefix (by rfl)]",
            "  decide"])
    if node.size<=threshold or not node.children:
        local(name,node,p,expr,t)
    else:
        names=[]
        for j,c in enumerate(node.children):
            cn=f"{name}_{j:02d}"
            p2=refine(p,node.s,MOVES[j])
            e2=f"refine ({expr}) {slot(node.s)} (some {move(MOVES[j])})"
            if c.size>threshold:
                imports.add(emit_tree(c,p2,e2,cn,node.n,threshold))
            else:local(cn,c,p2,e2,node.n)
            names.append(cn)
        kids="byMove ["+", ".join(names)+"]"
        body.extend([
            f"def {name} : Audit := .split {node.n} {slot(node.s)} ({kids})",
            f"theorem {name}_checked : zipCheck {BOUND} ({expr}) {name} = true := by",
            f"  change (zipQueryOK {BOUND} ({expr}) {node.n} {slot(node.s)} && allMoves (fun mv => zipCheck {BOUND} (refine ({expr}) {slot(node.s)} (some mv)) ({kids} mv))) = true",
            "  simp only [Bool.and_eq_true]",
            "  refine ⟨by decide, allMoves_of _ ?_⟩",
            all_moves([n+"_checked" for n in names])])
    write(mod,imports,"\n".join(body))
    return mod


def collect(work):
    for folder,src,name in [
        ("agent47-raw112-cut","enumerate_fast.cpp","enumerate"),
        ("agent8-tnf-six","bank.cpp","bank"),
        ("agent47-raw111-cut","ngram_sparse.cpp","ngram")]:
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/folder/src),"-o",str(work/name)],check=True)
    subprocess.run([str(work/"enumerate"),PARENT],cwd=work,check=True)
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()=="7a5b361c09d3f0f8be56947baa6390bd1f0617bac39a26bddc8495e3badb9b99"
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==1819
    found=dict((int(i),c) for i,c in (l.split(":") for l in subprocess.check_output(
        [str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()))
    assert len(found)==1433
    misses=[row for j,row in enumerate(rows) if j not in found]
    assert len(misses)==386
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="5b92ebb47de7e0e1edc4eb3acb2fbcc5b0956856b283a87dd93f0a928511e0da"
    certs,deps={},{}
    def put(row,proof,mod=None):
        assert row not in certs,("duplicate",row)
        certs[row]=proof
        if mod:deps[row]=mod
    def proved(i,mod,ns):
        put(misses[i],f".proven ({ns}.table) ({ns}.never)",mod)
    def far(row,code):
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        put(row,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")
    for j,c in found.items():far(rows[j],c)
    emit_counter(misses,ROOT)
    emit_growth(misses,ROOT)
    emit_late(misses,ROOT)
    emit_aug(misses,ROOT)
    emit_pair(misses,ROOT,250)
    for line in (ROOT/"oneRA-ledger.txt").read_text().splitlines():
        if not line or line.startswith("#"):continue
        tag,*v=line.split()
        if tag=="F":
            code,*ids=v
            for i in map(int,ids):far(misses[i],code)
        elif tag=="N":
            i,k,n,l,r=map(int,v)
            res=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True)
            ident,data=res.split(maxsplit=1)
            assert int(ident)==i
            if n>50000:
                width,N,L,R,S=data.split()
                assert (int(width),int(N))==(k,n)
                record=search_sparse(" ".join([ident,width,width,N,L,R,S]),misses[i])
                mod=f"Raw54OneRASparseQuot{i}"
                emit_mask(ROOT,mod,record)
                ns="BB6.Agent32AsymNGram."+mod
            else:
                mod,ns=emit(ROOT,i,misses[i],data,width=k,module_name=f"Raw54OneRASparse{i}",expected=(n,l,r))
                fuse_sparse(ROOT,mod)
            proved(i,mod,ns)
        elif tag=="R":
            i,k,t0,p0,t1,p1,n,l,r,e=map(int,v)
            D,N,info=run_search(misses[i],(k,t0,p0,t1,p1)*2)
            assert D is not None,(i,N,info)
            E,S=info
            assert (N,len(D[0])//2,len(D[1])//2,edge_count(E))==(n,l,r,e),i
            mod=f"Raw54OneRARun{i}"
            emit_data(ROOT,mod,misses[i],D,E,S)
            proved(i,mod,"BB6.Agent32AsymNGram."+mod)
        elif tag=="H":
            i,n,s=v;i,n=int(i),int(n)
            sl=2*(ord(s[0])-65)+int(s[1])
            assert misses[i].count("---")==1 and parse(misses[i])[sl]=="---"
            put(misses[i],f".last {n} {slot(sl)}")
        elif tag=="C":
            for i in map(int,v):proved(i,"Raw54OneRACounter",f"BB6.Agent8Raw54.OneRACounter.M{i}")
        elif tag=="G":
            for i in map(int,v):proved(i,f"Raw54OneRAGrow{i}",f"BB6.Agent8Raw54.OneRAGrow.M{i}")
        elif tag=="A":
            for i in map(int,v):proved(i,f"Raw54OneRAAug{i}",f"BB6.Agent32AsymNGram.Raw54OneRAAug{i}")
        elif tag=="P":
            for i in map(int,v):proved(i,f"Raw54OneRAPair{i}",f"BB6.Agent32AsymNGram.Raw54OneRAPair{i}")
        elif tag=="Z":
            i,e,k,r,b=map(int,v)
            assert i==79 and (e,k,r,b)==(4953,566,1,194)
            proved(i,"Raw54OneRA79","BB6.Agent8Raw54.OneRA79")
        else:raise ValueError((tag,v))
    assert set(certs)==set(rows),[i for i,row in enumerate(misses) if row not in certs]
    return json.loads((work/"tree.json").read_text()),certs,deps

def enlarge_late(node,threshold):
    if node.children:
        for child in node.children:enlarge_late(child,threshold)
        node.size=sum(c.size for c in node.children)
    elif node.tag=="open" and node.text==".last 39446 (0,true)":
        node.size=threshold+1

def assemble(tree,certs,deps,threshold):
    stats=Counter()
    root=Node(tree,certs,deps,stats)
    assert stats==Counter(split=2765,cycle=47151,last=14626,open=1819),stats
    write("Raw54OneRABase",["Raw54OneRAParent"],"""abbrev parent : PartialMachine := BB6.Agent8Raw54.OneRALate.parent
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := BB6.Agent8Raw54.OneRALate.parent_root
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := BB6.Agent8Raw54.OneRALate.parent_nohalt""")
    enlarge_late(root,threshold)
    mod=emit_tree(root,parse(PARENT),"parent","oneRAShardRoot",0,threshold)
    write("Raw54OneRACut",[mod,"Raw54OneRALate"],f"""theorem checked : zipCheck {BOUND} parent oneRAShardRoot = true := oneRAShardRoot_checked
theorem cover : ∀ m, compatible parent m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} parent oneRAShardRoot parent_root parent_nohalt checked).sound
theorem lower_bound39447 (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : {BOUND} ≤ B := by
  obtain ⟨m, hm, hh, hd⟩ := BB6.Agent8Raw54.OneRALate.M39447.attained
  have hb := h m hm 39446 0 hh hd
  omega
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ {BOUND} ≤ B := by
  constructor
  · exact lower_bound39447 B
  · intro h m hm k d hk hd
    exact Nat.le_trans (cover m hm k d hk hd) h
#print axioms cover
#print axioms exact_threshold""")
    print(stats,"root module",mod,"shards",len(list(ROOT.glob("Raw54OneRAShard*.lean"))),flush=True)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--threshold",type=int,default=50)
    a=ap.parse_args()
    assert a.threshold>0
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps=collect(Path(d))
        assemble(tree,certs,deps,a.threshold)
if __name__=="__main__":main()
