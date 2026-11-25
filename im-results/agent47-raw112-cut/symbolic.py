"""Reconstruct all known raw112 proof candidates; retain the exact two residual leaves."""
from pathlib import Path
import hashlib, sys, subprocess, tarfile
ROOT=Path(__file__).resolve().parent
for d in ("agent31-three-hole-tnf","agent47-raw111-cut","agent47-raw115-cut","agent47-raw114-cut"):
    sys.path.insert(0,str(ROOT.parent/d))
import generate_sweeps as pump
from generate_four_hole import masks,parse
import counter as c
import emit_sparse
c.tab=c.pump.tab
hard=[]
def generate(rows,work):
    global hard
    with tarfile.open(ROOT/"inductive-generators.tar.xz") as ar:
        for member in ar.getmembers():
            if not member.isfile() or Path(member.name).name!=member.name: raise ValueError(member.name)
        ar.extractall(ROOT,filter="data")
    hard=(ROOT/"hard.txt").read_text().splitlines()
    assert len(hard)==131 and hashlib.sha256((ROOT/"hard.txt").read_bytes()).hexdigest()=="23805b6953da558d904471078a742f87767945ec835afd5ebe602fbb68d32f69"
    assert len(set(hard))==131 and set(hard)<=set(rows)
    for f in ("make_poly.py","make_affine.py","make_103.py","make_binary.py","make_6.py"):
        p=ROOT/f; src=p.read_text(); p.write_text(src.replace("import counter as c","import counter as c\nc.tab=c.pump.tab")); subprocess.run([sys.executable,str(p)],check=True)
    known={}; imports={}
    def add(i,cert,module=None):
        row=hard[i]; assert row not in known
        known[row]=cert
        if module: imports[row]=module
    for line in (ROOT/"far-extra.txt").read_text().splitlines():
        i,code=line.split();i=int(i)
        d,D,L,R,z=masks(parse(hard[i]),int(code[0]),[int(v,16) for v in code[1:]])
        add(i,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")
    for line in (ROOT/"late.txt").read_text().splitlines():
        i,n,s=map(int,line.split())
        assert hard[i].count("---")==1
        add(i,f".last {n} ({s//2},{str(bool(s%2)).lower()})")
    exe=work/"ngram_sparse"
    subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/"agent47-raw111-cut"/"ngram_sparse.cpp"),"-o",str(exe)],check=True)
    for line in (ROOT/"ngram.txt").read_text().splitlines():
        i,k,*expected=map(int,line.split())
        out=subprocess.check_output([str(exe),str(k)],input=f"{i} {hard[i]}\n",text=True)
        ident,data=out.strip().split(maxsplit=1);assert int(ident)==i
        name,ns=emit_sparse.emit(ROOT,i,hard[i],data,width=k,module_name=f"Raw112Sparse{i}",expected=expected)
        add(i,f".proven {ns}.table {ns}.never",name)
    for i in (6,23,27,32,33,34,35,51,62,72,73,100,101,102,103,106,107,108,121):
        name=f"Raw112Counter{i}";ns=f"BB6Coverage.Agent31Pump.{name}"
        assert (ROOT/(name+".lean")).is_file()
        add(i,f".proven {ns}.table {ns}.never",name)
    assert set(hard)-set(known)=={hard[10],hard[15]}
    n=0
    for i,row in enumerate(rows):
        if row in hard: continue
        p=pump.parse(row); ans=pump.candidate(p,pump.concrete_events(p));assert ans is not None,row
        code,info=pump.generate(i,p,ans);name=f"Raw112Symbol{i}";ns=f"BB6Coverage.Agent31Pump.{name}"
        (ROOT/(name+".lean")).write_text("\n\n".join(["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {ns}","open BB6Coverage",code,f"end {ns}"])+"\n")
        known[row]=f".proven {ns}.M{i}.table {ns}.M{i}.never";imports[row]=name;n+=1
    assert n==435 and len(known)==564
    return known,imports
