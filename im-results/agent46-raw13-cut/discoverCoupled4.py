"""Solve exactly the remaining hard one-hole leaves of the raw13 #1093
four-hole cylinder. Candidate discovery only; the Lean tree consumes explicit
witnesses. No re-search of the accepted three-hole cylinder."""
import concurrent.futures
import json, subprocess, sys, tempfile
from pathlib import Path
from autoword import infer, step
from discover_frontier import fixture

D=Path(__file__).resolve().parent

def auto(t):
    r=infer(t,limit=100000,budget=30)
    if r and r[0]!="hole":
        return ("auto",fixture(t,r))
    if r and r[0]=="hole":
        q,l,x=0,"",""
        for i in range(r[1]):
            q,l,x=step(t,(q,l,x))
        return ("last",[t,r[1],2*q+int(l[0] if l else "0")])
    return ("unresolved",t)

def main():
    raw=(D/"coupled4-hard.txt").read_text().split()
    assert len(raw)==len(set(raw))==62
    assert all(len(t)==36 and t.count("---")==1 for t in raw)
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/"far5"
        subprocess.run(["g++","-O3","-std=c++17",str(D/"frontier_far5.cpp"),"-o",str(exe)],check=True)
        p=subprocess.run([str(exe)],input="\n".join(raw)+"\n",text=True,capture_output=True,check=True)
    far=[]
    for line in p.stdout.splitlines():
        t,rev,d=line.split()
        far.append([t,int(rev),d])
    remaining=p.stderr.split()
    assert len(far)+len(remaining)==len(raw)
    assert set(t for t,_,_ in far).isdisjoint(remaining)
    result={"far":far,"auto":[],"last":[],"unresolved":[]}
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        for tag,value in pool.map(auto,remaining):
            result[tag].append(value)
            print(tag, value if tag!="auto" else value["table"],flush=True)
    assert sum(map(len,result.values()))==len(raw)
    print({k:len(v) for k,v in result.items()},flush=True)
    Path(sys.argv[1]).write_text(json.dumps(result,indent=2)+"\n")

if __name__=="__main__":
    main()
