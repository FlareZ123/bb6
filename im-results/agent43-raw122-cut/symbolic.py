"""Untrusted candidate generation for raw122. All returned certificates must
pass the original-source Lean checker. Absent candidates remain unresolved."""
from pathlib import Path
from functools import lru_cache
import sys,subprocess,json
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
    plans={x["id"]:x for x in json.loads((ROOT/"long-plans.json").read_text())}
    direct_plans={x["table"]:x for x in json.loads((ROOT/"direct_certificates.json").read_text())}
    for i,row in rows:
        if row in direct_plans:
            plan=direct_plans[row]
            j=plan["id"]
            if j in (28,29,32):
                name="Raw122DirectSmall"
            else:
                import direct_cert
                direct_cert.generate(plan,ROOT)
                name=f"Raw122Direct{j}"
            ns=f"BB6Coverage.Agent31Pump.Raw122DirectGrowth.M{j}"
            certs[row]=f".proven {ns}.table {ns}.never"
            imports[row]=name
            continue
        if i in plans:
            plan=plans[i];assert plan["row"]==row
            import multi_sweep as multi
            W,R,C=multi.Word,multi.Rep,multi.Config
            def word(parts):return W.of(*(x if isinstance(x,str) else R(x["rep"]) for x in parts))
            st=C(plan["q"],word(plan["left"]),word(plan["right"]))
            tg=C(st.q,st.l.inc(),st.r.inc())
            p=pump.parse(row)
            res=multi.execute(p,st,tg,3000)
            assert res is not None
            name=f"Raw122Plan{i}"
            code,info=multi.generate(i,p,(plan["entry"],st,tg,res))
            ns=f"BB6Coverage.Agent31Pump.{name}"
            (ROOT/(name+".lean")).write_text("\n\n".join(["import SweepPumping","set_option maxRecDepth 100000",
              "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
              f"namespace {ns}","open BB6Coverage",code,f"end {ns}"])+"\n")
            certs[row]=f".proven {ns}.M{i}.table {ns}.M{i}.never"
            imports[row]=name
            continue
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
        if i in (3905,3906,3908):
            expected={3905:"1RB0RB_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC",
                      3906:"1RB0RC_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC",
                      3908:"1RB1LD_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC"}
            assert row==expected[i]
            ns=f"BB6Coverage.Agent31Pump.Raw122TailGrowth.M{i}"
            certs[row]=f".proven {ns}.table {ns}.never"
            imports[row]="Raw122TailGrowth"
            continue
        if i in (13479,25730,27624):
            sys.path.insert(0,str(ROOT.parent/"agent47-raw114-cut"))
            import multi_sweep as multi
            W,R,C=multi.Word,multi.Rep,multi.Config
            if i==13479:
                assert row=="1RB---_1RC0RA_0RD0LE_1LD1RE_0RB0LF_0LB1LC"
                t=34;st=C(2,W.of("01010",R("1010"),"010",R("10"),R("10")),W())
                tg=C(2,st.l.inc(),W())
            elif i==25730:
                assert row=="1RB0LD_1RC1LB_0RD1RF_1LD1RE_0RA0LF_---1RA"
                t=40;st=C(1,W(),W.of("1111111",R("1111"),R("1111"),R("1111")))
                tg=C(1,W(),st.r.inc())
            else:
                assert row=="1RB0LE_1RC0LA_0RD1RB_1LD1RE_1LB0LF_---1RE"
                t=1;st=C(1,W.of("01",R("111111"),R("111111")),W())
                tg=C(1,st.l.inc(),W())
            p=pump.parse(row)
            res=multi.execute(p,st,tg,3000)
            assert res is not None
            name=f"Raw122Long{i}"
            code,info=multi.generate(i,p,(t,st,tg,res))
            ns=f"BB6Coverage.Agent31Pump.{name}"
            source="\n\n".join(["import SweepPumping","set_option maxRecDepth 100000",
              "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
              f"namespace {ns}","open BB6Coverage",code,f"end {ns}"])
            (ROOT/(name+".lean")).write_text(source+"\n")
            certs[row]=f".proven {ns}.M{i}.table {ns}.M{i}.never"
            imports[row]=name
            print(i,"long sweep",info,flush=True)
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
