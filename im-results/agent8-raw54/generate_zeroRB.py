"""Generate the complete exact-threshold proof for the Raw54 E0=0RB child."""
from collections import Counter
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile, sys
from generate_rf_witnesses import ROOT, masks, parse
from generate_ra import Node, zrun, table, refine, all_moves, slot, move, MOVES, fuse_sparse
from generate_digit_sections import emit as emit_digits, ZERO_RB_IDS
from generate_zeroRB_special import emit as emit_special
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
from emit_sparse import emit
PARENT="1RB---_1RC---_0RD---_1LD0LE_0RB0LE_------"
BOUND=390
NS="BB6.Agent8Raw54.ZeroRB"
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent8Raw54.ZeroRB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
"""
def write(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join("import "+m+"\n" for m in sorted(set(imports)))+HEADER+body+"\nend "+NS+"\n")

def emit_tree(node,p,expr,name,t,threshold):
    mod="Raw54ZeroRBShard"+name.removeprefix("zeroRBShard").replace("_","X")
    imports={"Raw54ZeroRBBase"}
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
    assert hashlib.sha256(raw).hexdigest()=="831a2c2f191c3161d3dd0956622384013f0c6b18ab0cd7f096bc73b4bbb9e616"
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==1778
    found=dict((int(i),c) for i,c in (l.split(":") for l in subprocess.check_output(
        [str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()))
    assert len(found)==1370
    misses=[row for j,row in enumerate(rows) if j not in found]
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="92711eb390829f5984a729938926d5b07f3285e6a43a8c96bf933cf37dfa2e60"
    certs,deps={},{}
    def put(row,proof,mod=None):
        assert row not in certs,("duplicate",row)
        certs[row]=proof
        if mod:deps[row]=mod
    def proved(i,mod,ns,arg=""):
        put(misses[i],f".proven ({ns}.table{arg}) ({ns}.never{arg})",mod)
    far={rows[j]:c for j,c in found.items()}
    for line in (ROOT/'zeroRB-far-groups.txt').read_text().splitlines():
        code,indices=line.split()
        for i in map(int,indices.split(',')):
            assert misses[i] not in far
            far[misses[i]]=code
    assert len(far)==1740
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        put(row,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")
    i,k,n,l,r=355,13,855,93,130
    res=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True)
    ident,data=res.split(maxsplit=1)
    assert int(ident)==i
    mod,ns=emit(ROOT,i,misses[i],data,width=k,module_name=f"Raw54ZeroRBSparse{i}",expected=(n,l,r))
    fuse_sparse(ROOT,mod)
    proved(i,mod,ns)
    emit_digits(misses,ROOT)
    for i in ZERO_RB_IDS:
        proved(i,f"Raw54ZeroRBDigit{i}",f"BB6.Agent8Raw54.ZeroRB.M{i}")
    emit_special(misses,ROOT)
    assert misses[51]=="1RB0LF_1RC1RA_0RD0RB_1LD0LE_0RB0LE_---1LA"
    for i in (51,162,393):
        proved(i,f"Raw54ZeroRB{i}",f"BB6.Agent8Raw54.ZeroRB.M{i}")
    assert set(certs)==set(rows),[i for i,row in enumerate(misses) if row not in certs]
    assert len(deps)==38
    return json.loads((work/"tree.json").read_text()),certs,deps
def assemble(tree,certs,deps,threshold):
    stats=Counter()
    root=Node(tree,certs,deps,stats)
    assert stats==Counter(split=997,cycle=16539,last=4615,open=1778),stats
    write("Raw54ZeroRBBase",["Raw54ZeroRBLate"],"""abbrev parent : PartialMachine := BB6.Agent8Raw54.ZeroRBLate.parent
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := BB6.Agent8Raw54.ZeroRBLate.parent_root
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := BB6.Agent8Raw54.ZeroRBLate.parent_nohalt""")
    mod=emit_tree(root,parse(PARENT),"parent","zeroRBShardRoot",0,threshold)
    write("Raw54ZeroRBCut",[mod,"Raw54ZeroRBLate"],f"""theorem checked : zipCheck {BOUND} parent zeroRBShardRoot = true := zeroRBShardRoot_checked
theorem cover : ∀ m, compatible parent m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} parent zeroRBShardRoot parent_root parent_nohalt checked).sound
theorem lower_bound390 (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : {BOUND} ≤ B := by
  obtain ⟨m, hm, hh, hd⟩ := BB6.Agent8Raw54.ZeroRBLate.M390.attained
  have hb := h m hm 389 0 hh hd
  omega
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ {BOUND} ≤ B := by
  constructor
  · exact lower_bound390 B
  · intro h m hm k d hk hd
    exact Nat.le_trans (cover m hm k d hk hd) h
#print axioms cover
#print axioms exact_threshold""")
    print(stats,"root module",mod,"shards",len(list(ROOT.glob("Raw54ZeroRBShard*.lean"))),flush=True)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--threshold",type=int,default=50)
    a=ap.parse_args()
    assert a.threshold>0
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps=collect(Path(d))
        assemble(tree,certs,deps,a.threshold)
if __name__=="__main__":main()
