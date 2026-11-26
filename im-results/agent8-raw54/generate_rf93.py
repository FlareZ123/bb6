"""Compress the frozen RF93 sparse n-gram with the existing Agent32 quotient."""
from pathlib import Path
import subprocess, tempfile, sys, json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent32-raw59"))
from quotient_search import search
from emit_mask import emit
TABLE="1RB0LB_1RC0RC_0RD1RE_1LD0LE_1RF0LE_1RA---"
with tempfile.TemporaryDirectory() as tmp:
    exe=Path(tmp)/"ngram"
    subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/"agent47-raw111-cut/ngram_sparse.cpp"),"-o",str(exe)],check=True)
    line=subprocess.check_output([str(exe),"28"],input=f"93 {TABLE}\n",text=True).strip()
    i,k,n,L,R,S=line.split()
    assert (i,k,n)==("93","28","1005602")
    record=search(" ".join([i,k,k,n,L,R,S]),TABLE)
    assert record["states"]==31667,record
    assert [len(d)//2 for d in record["dfa"]]==[722,972]
    assert record["edges"]==2156
    (ROOT/"rf93-quotient.json").write_text(json.dumps(record,separators=(",",":"))+"\n")
    emit(ROOT,"Raw54RF93Quot",record)
