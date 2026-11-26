"""Generate the complete exact-threshold proof for the Raw54 E0=0LF child."""
from collections import Counter
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile, sys
from generate_rf_witnesses import ROOT, masks, parse
from generate_ra import Node, zrun, table, refine, all_moves, slot, move, MOVES, fuse_sparse
from generate_zeroLF_growth import emit_growth
from generate_zeroLF12 import emit_phase12
from generate_zeroLF_quotients import generate as emit_quotients
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
from emit_sparse import emit
PARENT="1RB---_1RC---_0RD---_1LD0LE_0LF0LE_------"
BOUND=1055
NS="BB6.Agent8Raw54.ZeroLF"
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent8Raw54.ZeroLF
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
"""
def write(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join("import "+m+"\n" for m in sorted(set(imports)))+HEADER+body+"\nend "+NS+"\n")

def emit_tree(node,p,expr,name,t,threshold):
    mod="Raw54ZeroLFShard"+name.removeprefix("zeroLFShard").replace("_","X")
    imports={"Raw54ZeroLFBase"}
    body=[]
    def local(n,c,p2,e2,prefix):
        imports.update(c.deps)
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
    assert hashlib.sha256(raw).hexdigest()=="375c5f5cc4ce825594a94feea4e9bac832eeaab851168d0fa8821c68e939910d"
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==1308
    found=dict((int(i),c) for i,c in (l.split(":") for l in subprocess.check_output(
        [str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()))
    assert len(found)==1089
    misses=[row for j,row in enumerate(rows) if j not in found]
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="d013ba549e3284f18092fd34491eb5e1cfc3cd262ea0a8d36c9ea9e6e823771b"
    certs,deps={},{}
    def put(row,proof,mod=None):
        assert row not in certs,("duplicate",row)
        certs[row]=proof
        if mod:deps[row]=mod
    def proved(i,mod,ns,arg=""):
        put(misses[i],f".proven ({ns}.table{arg}) ({ns}.never{arg})",mod)
    far={rows[j]:c for j,c in found.items()}
    for line in (ROOT/"zeroLF-mut.txt").read_text().splitlines():
        i,c=line.split(":")
        assert misses[int(i)] not in far
        far[misses[int(i)]]=c
    assert len(far)==1185
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        put(row,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")
    for line in (ROOT/"zeroLF-ngram.txt").read_text().splitlines():
        i,k,n,l,r=map(int,line.split())
        res=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True)
        ident,data=res.split(maxsplit=1)
        assert int(ident)==i
        mod,ns=emit(ROOT,i,misses[i],data,width=k,module_name=f"Raw54ZeroLFSparse{i}",expected=(n,l,r))
        fuse_sparse(ROOT,mod)
        proved(i,mod,ns)
    emit_growth(misses,ROOT)
    for line in (ROOT/"zeroLF-growth.txt").read_text().splitlines():
        i=int(line.split()[0])
        proved(i,f"Raw54ZeroLFGrow{i}",f"{NS}.M{i}")
    emit_phase12(misses,ROOT)
    proved(12,"Raw54ZeroLF12",f"{NS}.M12")
    for group,ids in [
        ("Growth13",[13,16,18]),
        ("CounterGroup",[2,19,124,89,4,21,126,92,6,23,128,95,93,94,88,91,97]),
        ("SpecialCounter",[8,25,98,130,99]),
        ("Binary",[35,37,38,40,41,42,59])]:
        for i in ids:proved(i,"Raw54ZeroLF"+group,"BB6.Agent8Raw54.ZeroLF"+group,f" .m{i}")
    emit_quotients(misses,ROOT)
    for line in (ROOT/"zeroLF-run-quotients.txt").read_text().splitlines():
        i=int(line.split()[0]);mod=f"Raw54ZeroLFRun{i}"
        proved(i,mod,"BB6.Agent32AsymNGram."+mod)
    assert misses[166].count("---")==1 and parse(misses[166])[3]=="---"
    put(misses[166],".last 1054 (1,true)")
    assert set(certs)==set(rows),[i for i,row in enumerate(misses) if row not in certs]
    assert len(deps)==122
    return json.loads((work/"tree.json").read_text()),certs,deps
def assemble(tree,certs,deps,threshold):
    stats=Counter()
    root=Node(tree,certs,deps,stats)
    assert stats==Counter(split=929,cycle=14910,last=5150,open=1308),stats
    write("Raw54ZeroLFBase",["Raw54ZeroLFLate"],"""abbrev parent : PartialMachine := BB6.Agent8Raw54.ZeroLFLate.parent
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := BB6.Agent8Raw54.ZeroLFLate.parent_root
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := BB6.Agent8Raw54.ZeroLFLate.parent_nohalt""")
    mod=emit_tree(root,parse(PARENT),"parent","zeroLFShardRoot",0,threshold)
    write("Raw54ZeroLFCut",[mod,"Raw54ZeroLFLate"],f"""theorem checked : zipCheck {BOUND} parent zeroLFShardRoot = true := zeroLFShardRoot_checked
theorem cover : ∀ m, compatible parent m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} parent zeroLFShardRoot parent_root parent_nohalt checked).sound
theorem lower_bound1055 (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : {BOUND} ≤ B := by
  obtain ⟨m, hm, hh, hd⟩ := BB6.Agent8Raw54.ZeroLFLate.M166.attained
  have hb := h m hm 1054 0 hh hd
  omega
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ {BOUND} ≤ B := by
  constructor
  · exact lower_bound1055 B
  · intro h m hm k d hk hd
    exact Nat.le_trans (cover m hm k d hk hd) h
#print axioms cover
#print axioms exact_threshold""")
    print(stats,"root module",mod,"shards",len(list(ROOT.glob("Raw54ZeroLFShard*.lean"))),flush=True)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--threshold",type=int,default=50)
    a=ap.parse_args()
    assert a.threshold>0
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps=collect(Path(d))
        assemble(tree,certs,deps,a.threshold)
if __name__=="__main__":main()
