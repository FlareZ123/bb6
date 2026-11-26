#!/usr/bin/env python3
"""Generate a complete, sharded LA child certificate from the frozen census."""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib, json, re, subprocess, sys, tarfile, tempfile
from generate_rb import fuse_sparse, slot, move, MOVES, masks, parse
from generate_la_witnesses import emit_sweeps
from la_multivar import emit_multi, SPECS as MULTI
ROOT=Path(__file__).resolve().parent
PARENT="1RB---_1RC---_0RD---_1LD0LE_1LA0LE_------"
B=545
NS="BB6.Agent8Raw54.LA"
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
"""
def emit(name,imports,body):
    (ROOT/(name+".lean")).write_text("".join("import "+m+"\n" for m in sorted(set(imports)))+HEADER+body+"\nend "+NS+"\n")
def census(work):
    for folder,src,name in [
        ("agent47-raw112-cut","enumerate_fast.cpp","enumerate"),
        ("agent8-tnf-six","bank.cpp","bank"),
        ("agent47-raw111-cut","ngram_sparse.cpp","ngram")]:
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/folder/src),"-o",str(work/name)],check=True)
    subprocess.run([str(work/"enumerate"),PARENT],cwd=work,check=True)
    tree=json.loads((work/"tree.json").read_text())
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()=="c6ce7be3631b4544b5528fd717af5628a4b885745f16a8170970ffcc049efb4f"
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==1342
    out=subprocess.check_output([str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True)
    found={int(i):v for i,v in (l.split(":") for l in out.splitlines())}
    assert len(found)==1178
    misses=[row for j,row in enumerate(rows) if j not in found]
    assert len(misses)==164
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="0abdd7b494f234417e9079f683c2066174dcd3649a5e89070baff4686af3220b"
    return tree,rows,found,misses

def witnesses(work,rows,found,misses):
    certs,imports={},{}
    def put(row,proof,mod=None):
        assert row not in certs,("duplicate witness",row)
        certs[row]=proof
        if mod:imports[row]=mod
    def proved(i,mod,ns,arg=""):
        put(misses[i],f".proven ({ns}.table{arg}) ({ns}.never{arg})",mod)
    far={rows[i]:v for i,v in found.items()}
    for l in (ROOT/"la-mutated.txt").read_text().splitlines():
        i,code=l.split(":")
        far[misses[int(i)]]=code
    assert len(far)==1252
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        put(row,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")
    sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
    from emit_sparse import emit as emit_ngram
    widths={4:[16,68,75],6:[31,51,67,82,87,102,105,121,123,132,137],
        8:[36,54,78,80,81,133,134],12:[32,34,52,58,106,107,109,141,142,147,148],
        16:[59,110,111,129,131],20:[135]}
    for k,ids in widths.items():
        for i in ids:
            out=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True).strip()
            ident,data=out.split(maxsplit=1)
            assert int(ident)==i
            _,n,L,R,_=data.split()
            def edges(s):return sum(int(x.split(":")[1]).bit_count() for x in s.rstrip(",").split(","))
            mod,ns=emit_ngram(ROOT,i,misses[i],data,width=k,module_name=f"Raw54LASparse{i}",expected=(int(n),edges(L),edges(R)))
            fuse_sparse(ROOT,mod)
            proved(i,mod,ns)
    for archive in ("la-proofs.tar.xz","la-hard.tar.xz"):
        with tarfile.open(ROOT/archive,"r:xz") as f:
            for m in f.getmembers():
                if m.isfile() and m.name.endswith(".lean"):
                    p=ROOT/Path(m.name).name
                    if not p.exists():p.write_bytes(f.extractfile(m).read())
    sweep_ids=[2,13,79,89,90,92,103,143,157,163]
    if not all((ROOT/f"Raw54LASweep{i}.lean").exists() for i in sweep_ids):
        emit_sweeps(misses,ROOT)
    for i in sweep_ids:proved(i,f"Raw54LASweep{i}",f"{NS}.M{i}")
    multi_ids=[s[0] for s in MULTI]
    if not all((ROOT/f"Raw54LAMulti{i}.lean").exists() for i in multi_ids):
        emit_multi(misses,ROOT)
    for i in multi_ids:proved(i,f"Raw54LAMulti{i}",f"{NS}.M{i}")
    for group,ids in [
        ("Nested",[60,62,63,64,65,66]),
        ("NestedD",[76,77,144,145,161,162]),
        ("Alternating",[48,55,56,69,70,122])]:
        for i in ids:proved(i,"Raw54LA"+group,NS+"."+group,f" .m{i}")
    for i in [119,138]:proved(i,"Raw54LANestedTwo",f"{NS}.M{i}")
    for i in [37,61,104]:proved(i,f"Raw54LA{i}",f"{NS}.M{i}")
    for i,arg in [(126," false"),(127," true")]:proved(i,"Raw54LAPair126",NS+".Pair126",arg)
    remaining={i for i,row in enumerate(misses) if row not in certs}
    assert remaining=={27,49,94,108},remaining
    # Resolve archived source names by theorem namespace; exact table equality
    # is independently enforced by the original Lean checker.
    for p in sorted(ROOT.glob("Raw54LA*.lean")):
        src=p.read_text()
        for match in re.finditer(r"^namespace ("+re.escape(NS)+r"\.M(\d+))\s*$",src,re.M):
            ns,i=match[1],int(match[2])
            if i not in remaining:continue
            section=src[match.end():].split("\nend "+ns,1)[0]
            if re.search(r"^def table\b",section,re.M) and re.search(r"^theorem never\b",section,re.M):
                proved(i,p.stem,ns)
                remaining.remove(i)
    if remaining:
        print("Missing tables", [(i,misses[i]) for i in sorted(remaining)],flush=True)
        for arc in ("la-proofs.tar.xz","la-hard.tar.xz"):
            with tarfile.open(ROOT/arc,"r:xz") as archive:
                print(arc,archive.getnames(),flush=True)
    assert not remaining,("missing archived theorem namespace",remaining)
    assert set(certs)==set(rows)
    print("Complete leaf ledger:",len(certs),"FAR",len(far),"semantic",len(imports),flush=True)
    return certs,imports

def assemble(tree,certs,imports):
    stats=Counter()
    def visit(t):
        stats[t[0]]+=1
        if t[0]=="split":
            assert len(t[3])==24
            for c in t[3]:visit(c)
    visit(tree)
    assert stats==Counter(split=1816,cycle=27205,last=13222,open=1342),stats
    def count(t):return sum(count(c) for c in t[3]) if t[0]=="split" else 1
    def deps(t):
        if t[0]=="open":return {imports[t[1]]} if t[1] in imports else set()
        if t[0]=="split":return set().union(*(deps(c) for c in t[3]))
        return set()
    def render(t):
        tag,*v=t
        if tag=="open":return certs[v[0]]
        if tag=="last":return f".last {v[0]} {slot(v[1])}"
        if tag=="cycle":
            e,k,r,b=v
            return f".cycle {e} {k} {str(r).lower()} ({b})"
        assert tag=="split"
        n,s,kids=v
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(render(c) for c in kids)+"])"
    def checked(name,p):
        return f"""theorem {name}_checked : zipCheck {B} ({p}) {name} = true := by
  rw [← checkAt_eq {B} ({p}) {name} 0 start rfl]
  decide
"""
    def shard(t,p,name):
        tag,*v=t
        mod="Raw54LAShard"+name.removeprefix("laShard").replace("_","X")
        if tag!="split" or count(t)<=50:
            emit(mod,["Raw54LABase",*deps(t)],f"def {name} : Audit := {render(t)}\n"+checked(name,p))
            return mod
        n,s,kids=v
        modules=["Raw54LABase"];parts=[];names=[]
        for j,c in enumerate(kids):
            child=f"{name}_{j:02}"
            cp=f"refine ({p}) {slot(s)} (some {move(MOVES[j])})"
            if count(c)>50:
                modules.append(shard(c,cp,child))
            else:
                modules.extend(deps(c))
                parts.append(f"def {child} : Audit := {render(c)}\n"+checked(child,cp))
            names.append(child)
        ks=", ".join(names)
        parts.append(f"""def {name} : Audit := .split {n} {slot(s)} (byMove [{ks}])
theorem {name}_checked : zipCheck {B} ({p}) {name} = true := by
  change (zipQueryOK {B} ({p}) {n} {slot(s)} && allMoves (fun mv => zipCheck {B} (refine ({p}) {slot(s)} (some mv)) (byMove [{ks}] mv))) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+ "".join(f"  · exact {names[12*w+6*r+q]}_checked\n" for q,w,r in product(range(6),range(2),range(2))))
        emit(mod,modules,"\n".join(parts))
        return mod
    mod=shard(tree,"parent","laShardRoot")
    emit("Raw54LACut",[mod,"Raw54LAAttained"],"""theorem checked : zipCheck 545 parent laShardRoot = true := laShardRoot_checked
theorem cover : ∀ m, compatible parent m → WeightedBound 545 m :=
  (certifiedZip 545 parent laShardRoot parent_root parent_nohalt checked).sound
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ 545 ≤ B := by
  constructor
  · exact lower_bound B
  · intro h m hm k d hk hd
    exact Nat.le_trans (cover m hm k d hk hd) h
#print axioms cover
#print axioms exact_threshold
""")
    print(stats,"root module",mod,flush=True)

if __name__=="__main__":
    with tempfile.TemporaryDirectory() as d:
        work=Path(d)
        tree,rows,found,misses=census(work)
        certs,imports=witnesses(work,rows,found,misses)
        assemble(tree,certs,imports)
