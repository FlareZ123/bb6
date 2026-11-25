"""Generate and attach the 137 non-FAR source proof candidates."""
from pathlib import Path
from functools import lru_cache
import sys
import subprocess
import hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
sys.path.insert(0,str(ROOT.parent/"agent47-raw114-cut"))
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
import generate_sweeps as pump
import counter
import emit_sparse

def generate(rows,work):
    hard=(ROOT/"hard.txt").read_text().splitlines()
    assert len(hard)==10
    assert all(row in rows for row in hard)
    counter.main()
    sparse={0:(6,1344,128,13),1:(5,243,35,17),7:(17,3405,135,855),8:(3,160,9,16)}
    exe=work/"ngram_sparse"
    subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/"agent47-raw111-cut"/"ngram_sparse.cpp"),"-o",str(exe)],check=True)
    known={}
    for i,row in enumerate(hard):
        if i in sparse:
            width,*expected=sparse[i]
            out=subprocess.check_output([str(exe),str(width)],input=f"{i} {row}\n",text=True)
            ident,data=out.strip().split(maxsplit=1)
            assert int(ident)==i
            known[row]=emit_sparse.emit(ROOT,i,row,data,width=width,module_name=f"Raw115Sparse{i}",expected=expected)
        else:
            name=f"Raw115Counter{i}"
            known[row]=(name,f"BB6Coverage.Agent31Pump.{name}")
    certs={};imports={};manifest=[]
    for i,row in enumerate(rows):
        if row in known:
            name,ns=known[row]
        else:
            p=pump.parse(row)
            ans=pump.candidate(p,pump.concrete_events(p))
            assert ans is not None,row
            code,info=pump.generate(i,p,ans)
            manifest.append(f"{row} "+",".join(map(str,info)))
            name=f"Raw115Symbol{i}"
            ns=f"BB6Coverage.Agent31Pump.{name}"
            source="\n\n".join(["import SweepPumping","set_option maxRecDepth 100000",
              "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
              f"namespace {ns}","open BB6Coverage",code,f"end {ns}"])
            (ROOT/(name+".lean")).write_text(source+"\n")
            ns+=f".M{i}"
        certs[row]=f".proven {ns}.table {ns}.never"
        imports[row]=name
    assert len(manifest)==127
    assert hashlib.sha256(("\n".join(manifest)+"\n").encode()).hexdigest()=="543bfc4d68aa2f1105e0f3fc8418183b52039b7d5350ed14aba9af6484b5c2bc"
    assert len(certs)==137
    return certs,imports
