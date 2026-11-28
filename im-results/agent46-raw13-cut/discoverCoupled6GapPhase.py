#!/usr/bin/env python3
"""Phase-aware BiDFA candidate discovery for the exact Raw13 p3 gap roster."""
from pathlib import Path
import json, subprocess, sys, tempfile

ROOT=Path(__file__).resolve().parent
IM=ROOT.parent
sys.path.insert(0,str(ROOT))
sys.path.insert(0,str(IM/"agent25-raw123"))
sys.path.insert(0,str(IM/"agent16-raw118"))
from discoverCoupled6GapSAT import TARGETS
from minimize_phase import minimize
from bidfa_emit import emit

def parse_dfa(token):
    count,payload=token.split(":",1)
    values=[int(x) for x in payload.split(",") if x]
    assert len(values)==2*int(count)
    return values

def main(outdir,cap=8000):
    out=Path(outdir);out.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="a46-p3-phase-") as td:
        exe=Path(td)/"phase"
        subprocess.run(["g++","-std=c++17","-O3",str(IM/"agent25-raw123"/"phase.cpp"),"-o",str(exe)],check=True)
        payload="".join(f"{i} {t}\n" for i,t in enumerate(TARGETS))
        r=subprocess.run([str(exe),str(cap)],input=payload,text=True,capture_output=True,check=True,timeout=1200)
    (out/"stdout.txt").write_text(r.stdout)
    (out/"stderr.txt").write_text(r.stderr)
    hits=[]
    for line in r.stdout.splitlines():
        parts=line.split()
        if len(parts)!=14:
            raise RuntimeError("unexpected phase output: "+line[:300])
        i=int(parts[0]); table=TARGETS[i]
        left=parse_dfa(parts[12]); right=parse_dfa(parts[13])
        dl,dr,states,edges=minimize(table,left,right)
        hits.append(dict(table=table,status="ok",dfa=[dl,dr],states=states,edges=edges))
    (out/"bank.json").write_text(json.dumps(hits,separators=(",",":"))+"\n")
    src=["import BiDFA","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
         "namespace BB6.Agent46Raw13Coupled6GapPhase",
         "open BB6Coverage BB6Coverage.Agent16BiDFA"]
    for i,x in enumerate(hits):
        code,n,e=emit(i,x["table"],*x["dfa"])
        assert (n,e)==(x["states"],x["edges"])
        src.append(code)
    src += ["end BB6.Agent46Raw13Coupled6GapPhase",""]
    (out/"Raw13Coupled6GapPhase.lean").write_text("\n".join(src))
    print("phase hits",len(hits),"of",len(TARGETS),flush=True)
    for x in hits: print(x["table"],x["states"],x["edges"],flush=True)

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/a46-gap-phase",
         int(sys.argv[2]) if len(sys.argv)>2 else 8000)
