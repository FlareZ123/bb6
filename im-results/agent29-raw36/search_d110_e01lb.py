#!/usr/bin/env python3
"""Search finite inverse-stack nonhalting certificates for ONE unproved BB6 table.

Target is the sole unresolved complete/one-hole literal in Raw36 D1=0RE
/ E0=1LB after the accepted FAR + regular-stack discovery banks.
This search is *not a mathematical proof*. Successful parameters must be
emitted and accepted by the independent Lean TwoSidedAutomata kernel checker.
"""
import argparse,hashlib,json,random,signal,sys,time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent7-raw36-b1le"))
from stack_candidates import replay
from scan_structured import seeds as old_seeds

TARGET="1RB---_1RC1LC_0RD1RF_0LD0RE_1LB1RA_1RE0LF"
assert len(TARGET.replace("_",""))==36
MACHINE=tuple(TARGET.replace("_","")[j:j+3] for j in range(0,36,3))
PARAMS=[]
def make_candidates():
    rnd=random.Random(20261128)
    old={tuple(v) for v in old_seeds(200)[0]}
    out=[]
    for k in range(1,17):
        out.append(("n",k))
    for k in range(1,13):
        for c in range(1,17):
            for m in (2,3,4,5,6,7,8,9,10,11,12,14,16):
                out.append(("r",k,c,m))
    mods=list(range(2,35))+[36,40,48,64,72,80,96,112,128,144,160,192,224,256]
    for k in range(0,13):
        for m in mods:
            for b in (2,3,4,5,8,16):
                out.append(("m",k,m,b))
    for k in range(0,9):
        for period in range(1,9):
            pm=(1<<period)-1
            masks={0,pm,1,pm//2,pm^1,int("10"*period,2)&pm,
                   int("01"*period,2)&pm}
            for _ in range(12):
                masks.add(rnd.randrange(0,pm+1))
            for typ in (0,1):
                for init in (0,1,2,3):
                    for mask in sorted(masks):
                        out.append(("p",k,period,typ,mask,init))
    # Full targeted deterministic sweep, no accepted prior 200-param retreading.
    out=[tuple(v) for v in out if v not in old]
    seen=set();dedup=[]
    for v in out:
        if v in seen:continue
        seen.add(v);dedup.append(v)
    assert len(dedup)>5000
    rnd.shuffle(dedup)
    return dedup

def timed_out(*_):
    raise TimeoutError("candidate inverse-stack replay exceeded bound")

def trial(p):
    v=(*p,None)
    signal.signal(signal.SIGALRM,timed_out)
    signal.setitimer(signal.ITIMER_REAL,0.3)
    try:
        _,n,_,_,_,_=replay(MACHINE,v)
        return [list(p),n,"FOUND"]
    except (AssertionError,IndexError,ValueError,MemoryError,
            ZeroDivisionError,RecursionError,OverflowError,TimeoutError):
        return [p[0],None,"REJECT"]
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--max",type=int,default=6000)
    ap.add_argument("--workers",type=int,default=3)
    a=ap.parse_args()
    assert 100<=a.max<=20000 and 1<=a.workers<=8
    candidates=make_candidates()
    # Prioritize low complexity by cheap manifest order after seeded shuffle;
    # keep a deterministic, sparse exploration across param families.
    candidates=candidates[:a.max]
    start=time.monotonic()
    counts=Counter();found=[]
    with Pool(a.workers) as pool:
        for j,(params,n,status) in enumerate(pool.imap_unordered(trial,candidates,chunksize=1),1):
            counts[status]+=1
            if status=="FOUND":
                found.append({"params":params,"finite_states":n,"kind":params[0]})
                print("CANDIDATE_FOUND",json.dumps(found[-1]),flush=True)
                if len(found)>=6:pool.terminate();break
            if j%500==0:
                print("PROGRESS",j,len(candidates),"found",len(found),
                      "secs",round(time.monotonic()-start,1),flush=True)
    report={
      "kind":"inverse-stack candidate search, NOT source acceptance",
      "machine":TARGET,
      "machine_digest":hashlib.sha256(TARGET.encode()).hexdigest(),
      "seed":20261128,
      "prior_parameter_count":len(old_seeds(200)[0]),
      "candidate_universe":len(make_candidates()),
      "selected_trials":len(candidates),
      "completed_trials":sum(counts.values()),
      "result_count":len(found),
      "successful_parameters":found,
      "elapsed_s":round(time.monotonic()-start,2)}
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report,sort_keys=True),flush=True)
if __name__=="__main__":main()
