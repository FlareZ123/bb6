#!/usr/bin/env python3
"""Construct the complete RF child audit from the frozen first-hole census.

Discovery is untrusted: original Lean zipCheck/checkAt_eq validates every
branch and exact table, and certifiedZip supplies the original weighted bound.
All expensive leaf certificates are regenerated from their accepted recipes.
"""
from collections import Counter
from pathlib import Path
import argparse, hashlib, json, subprocess, tarfile, tempfile
from generate_rf_witnesses import ROOT, PARENT, census, emit_ngrams, masks, parse
from generate_rf_growth import emit_growth
from generate_ra import Node, zrun, table, refine, all_moves, slot, move, MOVES

BOUND = 14389
NS = "BB6.Agent8Raw54.RF"
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent8Raw54.RF
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
"""

def write(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join("import "+m+"\n" for m in sorted(set(imports)))+HEADER+body+"\nend "+NS+"\n")

def collect(work):
    misses=census(work)
    rows=(work/"open.txt").read_text().splitlines()
    found=dict((int(i),c) for i,c in (l.split(":") for l in subprocess.check_output(
        [str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()))
    assert misses==[row for j,row in enumerate(rows) if j not in found]
    certs, deps = {}, {}
    def put(row,proof,mod=None):
        assert row not in certs,("duplicate",row)
        certs[row]=proof
        if mod:deps[row]=mod
    def proved(i,mod,ns,arg=""):
        put(misses[i],f".proven ({ns}.table{arg}) ({ns}.never{arg})",mod)
    far={rows[j]:c for j,c in found.items()}
    for ledger in ("rf-mutated.txt","rf-extra.txt"):
        for l in (ROOT/ledger).read_text().splitlines():
            i,c=l.split(":")
            assert misses[int(i)] not in far
            far[misses[int(i)]]=c
    assert len(far)==2008
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        put(row,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")

    sparse_ids={int(l.split()[0]) for l in (ROOT/"rf-ngram.txt").read_text().splitlines()}-{40,41,93}
    assert len(sparse_ids)==64
    emit_ngrams(work,misses,50000,sparse_ids)
    for i in sorted(sparse_ids):
        mod=f"Raw54RFSparse{i}"
        proved(i,mod,"BB6.Agent47SparseNGram."+mod)
    emit_growth(misses)
    growth_ids={int(l.split()[0]) for l in (ROOT/"rf-growth.txt").read_text().splitlines()}
    assert len(growth_ids)==57
    for i in sorted(growth_ids):
        proved(i,f"Raw54RFGrow{i}",f"{NS}.M{i}")

    with tarfile.open(ROOT/"rf-hard.tar.xz","r:xz") as f:
        for m in f.getmembers():
            if m.isfile() and m.name.endswith(".lean"):
                p=ROOT/Path(m.name).name
                content=f.extractfile(m).read()
                if p.exists(): assert p.read_bytes()==content,p
                else:p.write_bytes(content)
    for group,ids in [("Stack011",[0,10,11]),("Stack579",[57,59,63])]:
        for i in ids:proved(i,"Raw54RF"+group,NS+"."+group,f" .m{i}")
    for i in (61,62):
        proved(i,f"Raw54RF{i}",f"{NS}.M{i}")
    for i in (54,55,141,149):
        proved(i,f"Raw54RF{i}",f"BB6.Agent8Raw54.RF{i}")
    subprocess.run(["python",str(ROOT/"generate_rf93.py")],check=True)
    subprocess.run(["python",str(ROOT/"generate_rf_run_quotients.py")],check=True)
    for i,mod in [(69,"Raw54RF69RunQuot"),(93,"Raw54RF93Quot"),(144,"Raw54RF144RunQuot")]:
        proved(i,mod,"BB6.Agent32AsymNGram."+mod)
    for i,n,s in [(139,14388,11),(174,1048,3)]:
        assert misses[i].count("---")==1 and parse(misses[i])[s]=="---"
        put(misses[i],f".last {n} {slot(s)}")
    assert set(certs)==set(rows),[i for i,row in enumerate(misses) if row not in certs]
    print("complete RF ledger",len(certs),"FAR",len(far),"semantic",len(deps),"late",2,flush=True)
    return json.loads((work/"tree.json").read_text()),certs,deps

def emit_tree(node,p,expr,name,t,threshold):
    mod="Raw54RFShard"+name.removeprefix("rfShard").replace("_","X")
    imports={"Raw54RFBase"}
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

def assemble(tree,certs,deps,threshold):
    stats=Counter()
    root=Node(tree,certs,deps,stats)
    assert stats==Counter(split=2610,cycle=45064,last=12821,open=2146),stats
    mod=emit_tree(root,parse(PARENT),"parent","rfShardRoot",0,threshold)
    write("Raw54RFCut",[mod,"Raw54RFLate"],f"""theorem checked : zipCheck {BOUND} parent rfShardRoot = true := rfShardRoot_checked
theorem cover : ∀ m, compatible parent m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} parent rfShardRoot parent_root parent_nohalt checked).sound
theorem lower_bound14389 (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : {BOUND} ≤ B := by
  obtain ⟨m, hm, hh, hd⟩ := BB6.Agent8Raw54.RFLate.M139.attained
  have hb := h m hm 14388 0 hh hd
  omega
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ {BOUND} ≤ B := by
  constructor
  · exact lower_bound14389 B
  · intro h m hm k d hk hd
    exact Nat.le_trans (cover m hm k d hk hd) h
#print axioms cover
#print axioms exact_threshold""")
    print(stats,"root module",mod,"shards",len(list(ROOT.glob("Raw54RFShard*.lean"))),flush=True)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--threshold",type=int,default=50)
    a=ap.parse_args()
    assert a.threshold>0
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps=collect(Path(d))
        assemble(tree,certs,deps,a.threshold)
if __name__=="__main__":main()
