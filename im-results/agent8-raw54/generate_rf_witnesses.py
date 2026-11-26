#!/usr/bin/env python3
"""RF frozen census and reproducible individual FAR / sparse certificates."""
from pathlib import Path
import argparse, hashlib, subprocess, sys, tempfile
from generate_rb import masks, parse, fuse_sparse
ROOT = Path(__file__).resolve().parent
PARENT = "1RB---_1RC---_0RD---_1LD0LE_1RF0LE_------"

def census(work):
    for folder,src,name in [
        ("agent47-raw112-cut","enumerate_fast.cpp","enumerate"),
        ("agent8-tnf-six","bank.cpp","bank"),
        ("agent47-raw111-cut","ngram_sparse.cpp","ngram")]:
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/folder/src),"-o",str(work/name)],check=True)
    subprocess.run([str(work/"enumerate"),PARENT],cwd=work,check=True)
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()=="ae1d7c235351d32702026c6d6d416d01548c257aab30e98773ea88b81d63113c"
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==2146
    hits={int(l.split(":")[0]) for l in subprocess.check_output([str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()}
    assert len(hits)==1967
    misses=[s for j,s in enumerate(rows) if j not in hits]
    assert len(misses)==179
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="b5cc41348b6fb3a76c7abd71623b8b36f880a5c0579b7478df7c99b82d9e0461"
    return misses

def bools(x):return str(bool(x)).lower()
def emit_far(rows,mut):
    for i,code in mut.items():
        p=parse(rows[i]);rev=int(code[0]);d,D,L,R,z=masks(p,rev,[int(c,36) for c in code[1:]])
        out=['import FastFAR','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent8Raw54.RF','open BB6Coverage BB6Coverage.FAR']
        out+=[f'namespace M{i}','def table : PartialMachine := fun s => match s.1.val,s.2 with']
        for q,a in enumerate(p):
            if a!='---':out.append(f'  | {q//2},{bools(q%2)} => some (some ⟨{bools(int(a[0]))},{bools(a[1]=="R")},{ord(a[2])-65}⟩)')
        out+=['  | _,_ => none',f'def cert : FAR.Data {d} := ⟨0,{D},{L},{R},{z}⟩']
        arg='(reflectPartial table)' if rev else 'table'
        out+=[f'theorem checked : cert.fastValid {arg} = true := by decide','theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by']
        out+=['  exact reflectNever m (cert.sound (reflectPartial table) (cert.fastValid_sound _ checked) (reflectTable m) (reflectCompatible table m hm))' if rev else '  exact cert.sound table (cert.fastValid_sound _ checked) m hm','#print axioms never',f'end M{i}','end BB6.Agent8Raw54.RF']
        (ROOT/f'Raw54RFMut{i}.lean').write_text('\n'.join(out)+'\n')

def emit_ngrams(work,rows,max_states,ids=None):
    sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
    from emit_sparse import emit
    for i,k,n in (map(int,l.split()) for l in (ROOT/"rf-ngram.txt").read_text().splitlines()):
        if n>max_states or (ids is not None and i not in ids):continue
        line=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {rows[i]}\n",text=True).strip()
        ident,data=line.split(maxsplit=1)
        assert int(ident)==i
        _,ns,L,R,_=data.split()
        assert int(ns)==n
        def edges(s):return sum(int(x.split(":")[1]).bit_count() for x in s.rstrip(",").split(","))
        mod,_=emit(ROOT,i,rows[i],data,width=k,module_name=f"Raw54RFSparse{i}",expected=(n,edges(L),edges(R)))
        fuse_sparse(ROOT,mod)

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--sparse",action="store_true")
    ap.add_argument("--max-states",type=int,default=50000)
    ap.add_argument("--sparse-ids",type=int,nargs="+")
    args=ap.parse_args()
    with tempfile.TemporaryDirectory() as d:
        work=Path(d);rows=census(work)
        mut={int(i):c for i,c in (l.split(":") for l in (ROOT/"rf-mutated.txt").read_text().splitlines())}
        assert len(mut)==39
        extra={int(i):c for i,c in (l.split(":") for l in (ROOT/"rf-extra.txt").read_text().splitlines())}
        assert set(extra).isdisjoint(mut)
        emit_far(rows,mut|extra)
        if args.sparse:emit_ngrams(work,rows,args.max_states,args.sparse_ids)
