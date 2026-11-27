"""Discovery of the p4 five-hole ancestor; the p5 branch is a conditional graft.
No timeout is classified as a nonhalt. The trees are candidate certificates."""
import collections, concurrent.futures, json, pathlib, subprocess, sys, tempfile

D=pathlib.Path(__file__).resolve().parent
ROOT="1RB1LD1RC---1LA1RE---0LA---0RD------"
GRAFT="1RB1LD1RC---1LA1RE1LF0LA---0RD------"
MOVES=[str(w)+d+chr(65+q) for w in range(2) for d in "LR" for q in range(6)]

def tally(t, holes, cut, mass, counts, opened, times):
    tag=t[0];counts[tag]+=1
    if tag=="split":
        n,s,kids=t[1:]
        times.append(n)
        mass["halt"]+=25**(holes-1)
        for i,k in enumerate(kids):
            if k is None:continue
            q=i%6
            cm=collections.Counter()
            tally(k,holes-1,max(cut,q+1),cm,counts,opened,times)
            for label,v in cm.items():mass[label]+=v*(6-cut if q==cut else 1)
    else:
        mass[tag]+=25**holes
        if tag=="open":opened.append(t[1])
        if tag=="last":times.append(t[1])
        if tag=="graft":assert t[1]==GRAFT

def one(args):
    exe,files,mv=args
    raw=ROOT[:18]+mv+ROOT[21:]
    cut=max(5,ord(mv[-1])-64)
    p=subprocess.run([exe,str(D/"frontier-dfa-bank.txt"),*files],input=f"{raw} {cut} 4\n",text=True,capture_output=True,check=True,timeout=600)
    t=json.loads(p.stdout)
    mass,counts,opened,times=collections.Counter(),collections.Counter(),[],[]
    tally(t,4,cut,mass,counts,opened,times)
    assert sum(mass.values())==25**4
    print(mv,dict(counts),"max_query",max(times,default=0),flush=True)
    return {"move":mv,"mass":dict(mass),"counts":dict(counts),"open":opened,"max_query":max(times,default=0),"tree":t}

def main():
    out=pathlib.Path(sys.argv[1])
    with tempfile.TemporaryDirectory() as tmp:
        tmp=pathlib.Path(tmp);exe=tmp/"graft"
        subprocess.run(["g++","-std=c++17","-O3",str(D/"frontier_graft.cpp"),"-o",str(exe)],check=True)
        files=[tmp/x for x in ("far","auto","graft","late")]
        for f in files:f.write_text("")
        files[2].write_text(GRAFT+"\n")
        with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
            results=list(pool.map(one,[(str(exe),list(map(str,files)),m) for m in MOVES]))
    assert len(results)==24
    total=collections.Counter(halt=25**4)
    for x in results:total.update(x["mass"])
    assert total.total()==25**5
    out.write_text(json.dumps({"root":ROOT,"first_query":9,"slot":6,"graft":GRAFT,"mass":dict(total),"branches":results},separators=(",",":"))+"\n")
    print("TOTAL",dict(total),flush=True)
if __name__=="__main__":main()
