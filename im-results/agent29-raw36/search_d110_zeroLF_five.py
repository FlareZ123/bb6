#!/usr/bin/env python3
"""Pursue five exact previously unresolved D1=0RE E0=0LF literals.

Fresh inverse-stack families only, deterministic search. Any FOUND row
is an untrusted parametric candidate until the independent Lean kernel
checks its complete finite two-sided automaton proof.
"""
import argparse,hashlib,json,random,signal,sys,time
from pathlib import Path
from multiprocessing import Pool

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
sys.path.insert(0,str(HERE.parent/"agent7-raw36-b1le"))
from stack_candidates import replay
from search_d110_e01lb import make_candidates

TARGETS={
"0LF":[
"1RB0LE_1RC1RA_0RD0RB_0LD0RE_0LF0LD_1LA---",
"1RB0LE_1RC1RA_0RD0RB_0LD0RE_0LF0RD_1LA---",
"1RB0RB_1RC0RF_0RD0RA_0LD0RE_0LF---_1LB1LE",
"1RB0RC_1RC0RF_0RD0RA_0LD0RE_0LF---_1LB1LE",
"1RB1LF_1RC0RF_0RD1RA_0LD0RE_0LF---_1LA0LA",
],
# The seventh 0RF residual is a finite-halting candidate (2634 moves)
# and is handled by an exact Audit.last source proof, not NeverHalts search.
"0RF":[
"1RB0LA_1RC---_0RD0LA_0LD0RE_0RF1RA_1LF1LC",
"1RB0LA_1RC---_0RD0LD_0LD0RE_0RF1RA_1LE1LF",
"1RB0LA_1RC---_0RD1LA_0LD0RE_0RF1RA_1LE1LF",
"1RB0LA_1RC---_0RD1RD_0LD0RE_0RF1RA_1LE1LF",
"1RB1LD_1RC0LE_0RD---_0LD0RE_0RF1RA_1LF1LA",
"1RB1LD_1RC1RB_0RD---_0LD0RE_0RF1RA_1LF1LA",
],
}
assert all(len(t.replace("_",""))==36 for group in TARGETS.values() for t in group)
LITERALS=TARGETS["0LF"]
PARAMS=[]
def timed_out(*_):raise TimeoutError("regular-stack candidate timed out")
def worker(item):
    index,table,candidates=item
    machine=tuple(table.replace("_","")[j:j+3] for j in range(0,36,3))
    signal.signal(signal.SIGALRM,timed_out)
    start=time.monotonic()
    for j,p in enumerate(candidates,1):
        signal.setitimer(signal.ITIMER_REAL,0.17)
        try:
            ok,n,*_=replay(machine,(*p,None))
            assert ok
            found={"index":index,"table":table,"params":list(p),
                   "reachable":n,"tries":j,"seconds":round(time.monotonic()-start,2)}
            print("CANDIDATE_FOUND",json.dumps(found),flush=True)
            return found
        except (AssertionError,IndexError,ValueError,MemoryError,
                ZeroDivisionError,RecursionError,OverflowError,TimeoutError):
            pass
        finally:
            # Cancel the one-shot timer before changing the handler.  The
            # reverse order can race with SIGALRM and raise from finally,
            # discarding successful candidates already found by this worker.
            signal.setitimer(signal.ITIMER_REAL,0)
            signal.signal(signal.SIGALRM,signal.SIG_IGN)
            signal.signal(signal.SIGALRM,timed_out)
        if j%300==0:
            print("SCAN index",index,"tested",j,"elapsed",
                  round(time.monotonic()-start,1),flush=True)
    return {"index":index,"table":table,"status":"not found",
            "tries":len(candidates),"seconds":round(time.monotonic()-start,2)}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out",required=True,type=Path)
    ap.add_argument("--max",type=int,default=3500)
    ap.add_argument("--move",choices=sorted(TARGETS),default="0LF")
    a=ap.parse_args()
    global LITERALS
    LITERALS=TARGETS[a.move]
    assert 100<=a.max<=10000
    candidates=make_candidates()
    rr=random.Random(20261129)
    r=[p for p in candidates if p[0]=="r"]
    tail=[p for p in candidates if p[0]!="r"]
    rr.shuffle(r);rr.shuffle(tail)
    search=(r+tail)[:a.max]
    start=time.monotonic()
    args=[(i,LITERALS[i],search) for i in range(len(LITERALS))]
    with Pool(min(5,len(LITERALS))) as pool:
        results=list(pool.imap_unordered(worker,args,chunksize=1))
    report={"kind":"untrusted candidate search, NOT formal Cover",
      "target":f"Raw36 D1=0RE E0={a.move}",
      "seed":20261129,"param_count":len(search),
      "elapsed_s":round(time.monotonic()-start,2),
      "found":sum("params" in z for z in results),
      "results":sorted(results,key=lambda x:x["index"])}
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n")
    print("FINISHED",json.dumps(report,sort_keys=True),flush=True)
if __name__=="__main__":main()
