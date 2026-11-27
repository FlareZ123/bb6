"""Candidate SAT search for the last 1LC literal leaf; failure is not a verdict."""
import json, sys, time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent/"agent1-bidfa-sat"))
from synthesize import solve
sys.path.insert(0,str(D.parent/"agent32-raw59"))
from emit_rungram import witness
RAW="1RB1LD1RC1RE1LA1RE1LC0LA1RF0RD---0RA"
def try_one(args):
    l,r,ms=args
    t=time.monotonic()
    status,d=solve(RAW,l,r,ms)
    print(l,r,status,round(time.monotonic()-t,2),flush=True)
    if d is None:return None
    e,states=witness(RAW,*d)
    return dict(table=RAW,dfa=d,states=len(states),edges=sum(map(len,e)),params=["SAT",l,r,ms])
if __name__=="__main__":
    # Moderate budgets first; 4 workers and bounded overall runtime.
    sched=[(8,8,10000),(10,10,20000),(12,12,30000),(8,16,30000),
           (16,8,30000),(12,16,60000),(16,12,60000),(16,16,60000),
           (16,20,90000),(20,16,90000),(20,20,120000),(24,24,120000)]
    with ProcessPoolExecutor(max_workers=4) as pool:
        tasks=[pool.submit(try_one,x) for x in sched]
        for f in as_completed(tasks):
            z=f.result()
            if z is not None:
                (D/"coupled5-1LC-re-sat.json").write_text(json.dumps(z)+"\n")
                for task in tasks: task.cancel()
                print("SAT candidate preserved",z["states"],z["edges"],flush=True)
                break
