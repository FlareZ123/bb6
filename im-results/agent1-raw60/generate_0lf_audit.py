"""Build the exact raw60 A1=0LF conditional weighted certificate.

All discovered certificates are untrusted inputs; the existing kernel-checked
ZipThreeHoleAudit checker consumes every leaf, including explicit exceptions.
"""
from pathlib import Path
from collections import defaultdict
import json, subprocess, sys, os
import generate_0lf_pumps as pumps
import generate_0lf_unary as unary
import generate_0lf_second as second
import generate_0lf_sentinel as sentinel
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
import generate as audit
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
from emit_sparse import emit as emit_sparse
from emit_ngram import emit as emit_dense

def main():
    frontier=json.loads((ROOT/"0lf-frontier.json").read_text())
    opens=pumps.census(frontier)
    work=ROOT/"generated_0LF"
    manual=pumps.generate(frontier,opens)
    for name,gen in [("Raw60LFUnary",unary),("Raw60LFSecond",second),("Raw60LFSentinel",sentinel)]:
        src,mp=gen.generate(opens)
        (ROOT/(name+".lean")).write_text(src)
        assert not set(manual)&set(mp)
        manual.update(mp)
    for key,(mod,ns) in frontier["manual"].items():
        assert key not in manual
        manual[key]=[mod,ns,opens[int(key)]]
    sparse={int(i):k for i,k in frontier["sparse"].items()}
    dense=sorted(i for i,k in sparse.items() if k<=11)
    exe=work/"ngram"
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent1-ngram/ngram.cpp"),"-o",str(exe)],check=True)
    inp="".join(f"{i} {opens[i]}\n" for i in dense)
    result=subprocess.run([str(exe),"11"],input=inp,text=True,capture_output=True,check=True)
    certs=dict(line.split(maxsplit=1) for line in result.stdout.splitlines())
    assert set(map(int,certs))==set(dense),result.stderr
    for chunk in range(0,len(dense),8):
        mod=f"Raw60LFNGram{chunk//8:02}"
        ns="BB6.Agent1Raw60LFNGram."+mod
        code=["import NGramCertificate","set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {ns}","open BB6Coverage BB6.Agent1NGram"]
        for i in dense[chunk:chunk+8]:
            code.extend([f"namespace M{i}",emit_dense(i,opens[i],certs[str(i)]),
                         f"abbrev table := p{i}",
                         f"theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never{i} m hm",
                         f"end M{i}"])
            assert str(i) not in manual
            manual[str(i)]=[mod,f"{ns}.M{i}",opens[i]]
        code.append(f"end {ns}")
        (ROOT/(mod+".lean")).write_text("\n\n".join(code)+"\n")
    groups=defaultdict(list)
    for i,k in sparse.items():
        if k>11:groups[k].append(i)
    exe=work/"ngram_sparse"
    subprocess.run(["g++","-std=c++17","-O3",str(ROOT.parent/"agent47-raw111-cut/ngram_sparse.cpp"),"-o",str(exe)],check=True)
    for k,ids in groups.items():
        inp="".join(f"{i} {opens[i]}\n" for i in ids)
        certs=dict(line.split(maxsplit=1) for line in subprocess.check_output([str(exe),str(k)],input=inp,text=True).splitlines())
        assert set(map(int,certs))==set(ids)
        for i in ids:
            data=certs[str(i)]
            width,n,L,R,S=data.split()
            assert int(width)==k
            count=lambda s:sum(int(x.split(":")[1]).bit_count() for x in s.rstrip(",").split(","))
            mod,ns=emit_sparse(ROOT,i,opens[i],data,width=k,module_name=f"Raw60LFSparse{i}",expected=(int(n),count(L),count(R)))
            assert str(i) not in manual
            manual[str(i)]=[mod,ns,opens[i]]
    unresolved={str(i):opens[i] for i in frontier["unresolved"] if str(i) not in manual}
    assert len(manual)+len(unresolved)+1346==len(opens)
    spec={k:frontier[k] for k in ("bound","query","sha","stats")}
    spec.update(one=[],multi=[],ngram=[],manual=manual,unresolved=unresolved)
    audit.SPECS["0LF"]=spec
    os.environ["BB6_SHARD_AUDIT"]="1"
    audit.main("0LF")
    print("Exact 0LF unresolved",unresolved,flush=True)

if __name__=="__main__":main()
