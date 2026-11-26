"""Discover complete six-hole candidate certificates using the same strict classifier.

Input is raw13-open-residuals.txt (ID and exact literal table per row).
Output is a JSON catalogue keyed by stable caller-selected prefix + roster ID.
Only complete enumeration with all hard leaves assigned an explicit witness is retained.
Run generateBranch540.py KEY and the source audit before any coverage claim.
"""
import argparse,json,subprocess,tempfile,sys
from pathlib import Path
from autoword import infer
from generate_branch_base import describe
D=Path(__file__).resolve().parent

def run(cmd,inp=""):
    return subprocess.run(cmd,input=inp,text=True,capture_output=True,check=True)
def word(w):
    return [w.pre,w.block,word(w.post)] if w.block else w.pre
def fixture(t,r):
    j,f,(inc,path,(a,b)),_=r
    ops=[]
    for _,_,info in path:
        if info is None:
            if ops and isinstance(ops[-1],int):ops[-1]+=1
            else:ops.append(1)
        else:
            dr,lp,rp,I,O,k,L,R=info
            if dr=="L":lp,rp,L,R=rp,lp,R,L
            ops.append([dr,lp,rp,I,O,word(L),word(R),k])
    return dict(table=t,entry=j,family=[f.q,word(f.l),word(f.r)],inc=inc,ops=ops,a=a,b=b)
def discover(root,scan,far,empty,cap,budget):
    p=run([str(scan),str(D/"frontier-dfa-bank.txt"),str(empty),str(empty),"--discover",str(cap)],root+" 4 6\n")
    header,*rows=p.stdout.splitlines()
    raw,cut,holes,ok,n,*counts=header.split()
    assert raw==root and (cut,holes)==("4","6")
    if ok!="1":return None
    cnt=list(map(int,counts));hard=[row.split()[1] for row in rows]
    assert cnt[7]==len(hard) and sum(cnt)==int(n)
    q=run([str(far)],"\n".join(hard)+"\n")
    fw=[]
    for row in q.stdout.splitlines():
        t,rev,df=row.split();fw.append([t,int(rev),df])
    aw=[]
    for t in q.stderr.splitlines():
        result=infer(t,budget=budget)
        if not result or result[0]=="hole":
            print("unresolved",t,file=sys.stderr);return None
        aw.append(fixture(t,result))
    assert len(fw)+len(aw)==len(hard)
    return dict(root=root,counts=dict(cycle=cnt[2],last=cnt[1],split=cnt[4],halt=cnt[4],state=cnt[3],far=cnt[5]+len(fw),auto=len(aw)),far=fw,auto=aw)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("roster",type=Path)
    ap.add_argument("output",type=Path)
    ap.add_argument("--start",type=int,default=0)
    ap.add_argument("--stride",type=int,default=1)
    ap.add_argument("--limit",type=int,default=100)
    ap.add_argument("--cap",type=int,default=30)
    ap.add_argument("--budget",type=float,default=8)
    a=ap.parse_args()
    cat=json.loads(a.output.read_text()) if a.output.exists() else {}
    known={x["root"] for x in cat.values()}
    rows=[line.split() for line in a.roster.read_text().splitlines() if line.strip()]
    with tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp);scan=tmp/"scan";far=tmp/"far";empty=tmp/"empty";empty.touch()
        for file,exe in [("frontier_complete.cpp",scan),("frontier_far5.cpp",far)]:
            subprocess.run(["g++","-O3","-std=c++17",str(D/file),"-o",str(exe)],check=True)
        for i,raw in rows[a.start::a.stride][:a.limit]:
            if raw in known:continue
            try:describe(raw)
            except (AssertionError,KeyError):continue
            x=discover(raw,scan,far,empty,a.cap,a.budget)
            if not x:continue
            key="6"+str(i).zfill(5)
            assert key not in cat or cat[key]["root"]==raw
            cat[key]=x;known.add(raw)
            a.output.write_text(json.dumps(cat,indent=2)+"\n")
            print("candidate",key,raw,x["counts"],flush=True)
if __name__=="__main__":main()
