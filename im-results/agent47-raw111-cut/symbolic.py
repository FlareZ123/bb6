"""Discover the raw111 symbolic and n-gram candidates after FAR.
All generated Lean theorems must compile before any reduction is accepted.
"""
from pathlib import Path
from functools import lru_cache
import sys
import subprocess
import tempfile
import hashlib

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
import generate_sweeps as pump
pump.local=lru_cache(maxsize=200000)(pump.local)
sys.path.insert(0,str(ROOT.parent/"agent47-raw114-cut"))
import multi_sweep as multi
sys.path.insert(0,str(ROOT.parent/"agent1-ngram"))
from emit_ngram import emit as emit_ngram

def targeted(p,t):
    g=[(k,c.l.pre) for k,s,c in pump.concrete_events(p)
       if s=="R" and c.q==4 and c.r.pre==""]
    i=next(i for i,x in enumerate(g) if x[0]==t)
    a,b,c=[g[j][1] for j in range(i,i+3)]
    for w in multi.infer(a,b,c):
        if sum(isinstance(x,multi.Rep) for x in w.parts)<2: continue
        st=multi.Config(4,w,multi.Word())
        ta=multi.Config(4,w.inc(),multi.Word())
        res=multi.execute(p,st,ta)
        if res:return t,st,ta,res
    raise AssertionError(t)

def generate(rows,work):
    ng=dict(line.split() for line in (ROOT/"ngram-manifest.txt").read_text().splitlines())
    mu=dict(line.split() for line in (ROOT/"multi-manifest.txt").read_text().splitlines())
    known={"1RB---_1RC1RA_0RD0LE_1LD1RE_1LF0RC_0RA0LF":
        ("Raw111Ternary","BB6Coverage.Agent31Pump.Raw111Ternary"),
        "1RB0LD_1RC1LE_0RD0RF_1LD1RE_---0RC_0RC0RA":
        ("Raw111Triplet","BB6Coverage.Agent31Pump.Raw111Triplet"),
        "1RB0LF_1RC---_0RD1LF_1LD1RE_0RB0RC_0LA0RF":
        ("Raw111QuadCounter","BB6Coverage.Agent31Pump.Raw111QuadCounter")}
    certs={}
    imports={}
    single=[]
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent1-ngram"/"ngram.cpp"),"-o",str(work/"ngram")],check=True)
    for i,row in enumerate(rows):
        if row in known:
            name,ns=known[row]
        else:
            p=pump.parse(row)
            name=f"Raw111Symbol{i}"
            if row in ng:
                inp=f"{i} {row}\n"
                out=subprocess.check_output([str(work/"ngram"),ng[row]],input=inp,text=True)
                ident,data=out.strip().split(maxsplit=1)
                assert int(ident)==i and data.split()[0]==ng[row]
                ns=f"BB6.Agent1NGram.{name}"
                source="\n\n".join(["import NGramCertificate","set_option maxRecDepth 100000",
                  "set_option maxHeartbeats 0",f"namespace {ns}","open BB6Coverage BB6.Agent1NGram",
                  emit_ngram(str(i),row,data),f"end {ns}"])
                (ROOT/(name+".lean")).write_text(source+"\n")
                certs[row]=f".proven {ns}.p{i} {ns}.never{i}"
                imports[row]=name
                continue
            elif row == '1RB1LE_1RC---_0RD0RF_1LD1RE_1LB0RC_1LF0LA':
                w=multi.Word.of('0',multi.Rep('1'*12),'1'*8)
                st=multi.Config(0,multi.Word(),w)
                ta=multi.Config(0,multi.Word(),w.inc())
                res=multi.execute(p,st,ta,2000)
                assert res is not None
                code,info=multi.generate(i,p,(51,st,ta,res))
                assert info==(51,256,208),info
            elif row in mu:
                params=tuple(map(int,mu[row].split(",")))
                code,info=multi.generate(i,p,targeted(p,params[0]))
                assert info==params
            else:
                ans=pump.candidate(p,pump.concrete_events(p))
                if ans is None:continue
                code,info=pump.generate(i,p,ans)
                single.append(f"single {row} "+",".join(map(str,info)))
            ns=f"BB6Coverage.Agent31Pump.{name}"
            source="\n\n".join(["import SweepPumping","set_option maxRecDepth 100000",
              "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
              f"namespace {ns}","open BB6Coverage",code,f"end {ns}"])
            (ROOT/(name+".lean")).write_text(source+"\n")
            ns+=f".M{i}"
        certs[row]=f".proven {ns}.table {ns}.never"
        imports[row]=name
    assert len(single)==199,len(single)
    manifest="\n".join(sorted(single))+"\n"
    assert hashlib.sha256(manifest.encode()).hexdigest()=="aab7039ed0210df985e13993048903823052d7fa5e1d082dbd10c7462652c56d"
    assert len(certs)==222,len(certs)
    return certs,imports
