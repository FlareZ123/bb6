"""Untrusted candidate generation for raw122. All returned certificates must
pass the original-source Lean checker. Absent candidates remain unresolved."""
from pathlib import Path
from functools import lru_cache
import sys,subprocess
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
import generate_sweeps as pump
pump.local=lru_cache(maxsize=200000)(pump.local)
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
import emit_sparse
sys.path.insert(0,str(ROOT.parent/"agent1-ngram"))
from emit_ngram import emit as emit_ngram

def late_hole(p,B):
    if p.count("---")!=1:return None
    c=pump.C(0,0,0,pump.W(),pump.W())
    for t in range(B-8):
        s=2*c.q+int(c.l.head())
        if p[s]=="---":return t,s
        c=pump.step(p,c)
    return None

def generate(rows,work):
    certs={}; imports={}
    dense=work/"ngram"; sparse=work/"ngram_sparse"
    for src,exe in [(ROOT.parent/"agent1-ngram"/"ngram.cpp",dense),(ROOT.parent/"agent47-raw111-cut"/"ngram_sparse.cpp",sparse)]:
        subprocess.run(["g++","-std=c++17","-O3",str(src),"-o",str(exe)],check=True)
    for i,row in rows:
        if row=="1RB0RA_1RC1LF_0RD0RA_1LD1RE_---0LF_1LB0LB":
            ns="BB6Coverage.Agent31Pump.Raw122Counter3708"
            certs[row]=f".proven {ns}.table {ns}.never"
            imports[row]="Raw122Counter3708"
            continue
        if row=="1RB0LA_1RC---_0RD0RF_1LD1RE_1LA0LF_1RA1RE":
            import phase27510
            phase27510.generate()
            ns="BB6Coverage.Agent31Pump.Raw122Phases27510"
            certs[row]=f".proven {ns}.table {ns}.never"
            imports[row]="Raw122Phases27510"
            continue
        p=pump.parse(row)
        h=late_hole(p,7014)
        if h is not None:
            t,s=h;certs[row]=f".last {t} ({s//2},{str(bool(s%2)).lower()})"
            continue
        name=f"Raw122Symbol{i}"
        ans=pump.candidate(p,pump.concrete_events(p))
        if ans is not None:
            code,info=pump.generate(i,p,ans)
            ns=f"BB6Coverage.Agent31Pump.{name}"
            src="\n\n".join(["import SweepPumping","set_option maxRecDepth 100000",
              "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
              f"namespace {ns}","open BB6Coverage",code,f"end {ns}"])
            (ROOT/(name+".lean")).write_text(src+"\n")
            certs[row]=f".proven {ns}.M{i}.table {ns}.M{i}.never"
            imports[row]=name
            print(i,"sweep",info,flush=True);continue
        inp=f"{i} {row}\n"
        out=subprocess.run([str(dense),"10"],input=inp,text=True,capture_output=True,check=True).stdout.strip()
        if out:
            ident,data=out.split(maxsplit=1);assert int(ident)==i
            ns=f"BB6.Agent1NGram.{name}"
            src="\n\n".join(["import NGramCertificate","set_option maxRecDepth 100000",
              "set_option maxHeartbeats 0",f"namespace {ns}","open BB6Coverage BB6.Agent1NGram",
              emit_ngram(str(i),row,data),f"end {ns}"])
            (ROOT/(name+".lean")).write_text(src+"\n")
            certs[row]=f".proven {ns}.p{i} {ns}.never{i}"
            imports[row]=name;print(i,"dense",data.split()[:2],flush=True);continue
        # Sparse exact n-gram fixed points can be much larger. Keep only
        # modest ones here; expensive holdouts retain explicit residuals.
        for k in range(11,24):
            out=subprocess.run([str(sparse),str(k)],input=inp,text=True,capture_output=True)
            if out.returncode!=0:continue
            ident,data=out.stdout.strip().split(maxsplit=1)
            assert int(ident)==i
            _,n,L,R,S=data.split()
            if int(n)>20000:break
            edges=lambda s:sum(int(v).bit_count() for x,v in (a.split(":") for a in s.rstrip(",").split(",")))
            module,ns=emit_sparse.emit(ROOT,i,row,data,width=k,module_name=name,expected=(int(n),edges(L),edges(R)))
            certs[row]=f".proven {ns}.table {ns}.never"
            imports[row]=module;break
        if row not in certs:print(i,"unresolved",row,flush=True)
    return certs,imports
