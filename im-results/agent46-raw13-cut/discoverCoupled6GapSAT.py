#!/usr/bin/env python3
"""Targeted BiDFA synthesis for the exact currently uncovered Raw13 p3 leaf roster.

SAT output is candidate data. Every hit is re-expanded by Agent16's independent
fixed-point witness and compiled in Lean before it may enter the shared bank.
"""
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import json, sys, time

ROOT=Path(__file__).resolve().parent
IM=ROOT.parent
sys.path.insert(0,str(IM/"agent1-bidfa-sat"))
sys.path.insert(0,str(IM/"agent16-raw118"))
from synthesize import solve
from bidfa_emit import witness, emit

TARGETS=[
 "1RB1LD1RC0RB1LA1RE1LF0LA0RD0LC1LC---",
 "1RB1LD1RC1RB1LA1RE1LF0LA0RC0LD---0LE",
 "1RB1LD1RC1LB1LA1RE0LF0LA1RB0RC---0LA",
 "1RB1LD1RC0LB1LA1RE1LF0LA1LB0RE1LE---",
 "1RB1LD1RC0LD1LA1RE0RB0LA1RB0RF0LD---",
 "1RB1LD1RC0LD1LA1RE0RB0LA1RB0RF1LD---",
 "1RB1LD1RC0LD1LA1RE0RB0LA1RB0RF1RC---",
 "1RB1LD1RC0LD1LA1RE0RB0LA1RB0RF1RD---",
 "1RB1LD1RC1RA1LA1RE0LC0LA0RF1RB---0RB",
 "1RB1LD1RC0RA1LA1RE0RD0LA1RF1RB---0RB",
 "1RB1LD1RC1RA1LA1RE1RE0LA1RF1RB---0RA",
 "1RB1LD1RC0RB1LA1RE1LF0LA0LE1RC1LC---",
 "1RB1LD1RC1RA1LA1RE0LC0LA0RF1RC---0RB",
 "1RB1LD1RC0RB1LA1RE1LF0LA1LA1RC1LC---",
 "1RB1LD1RC0RB1LA1RE1LF0LA1LA1RC1LE---",
 "1RB1LD1RC0RB1LA1RE1LF0LA1LA1RE1LC---",
 "1RB1LD1RC0RB1LA1RE1LF0LA1LA1RE1LE---",
 "1RB1LD1RC---1LA1RE1LA0LA1RF1RE0LD0RE",
 "1RB1LD1RC0LD1LA1RE0RE0LA1RB1RF0LB---",
 "1RB1LD1RC---1LA1RE0RD0LA0RC1RF1LA0RD",
 "1RB1LD1RC---1LA1RE1LE0LA0RC1RF1LA0RD",
 "1RB1LD1RC---1LA1RE1RE0LA0RC1RF1LA0RD",
 "1RB1LD1RC0LC1LA1RE0RB0LA0RA1RF1RC---",
]
SCHEDULE=[
 (6,6,4000),(8,8,6000),(10,10,10000),
 (8,12,10000),(12,8,10000),(12,12,16000),
 (12,16,22000),(16,12,22000),(16,16,30000),
 (20,20,45000),
]
def search_one(item):
    i,table=item
    attempts=[]
    for L,R,ms in SCHEDULE:
        t=time.monotonic()
        status,d=solve(table,L,R,ms)
        attempts.append(dict(left=L,right=R,status=status,
                             seconds=round(time.monotonic()-t,3)))
        if d is None:
            continue
        edges,states=witness(table,d[0],d[1])
        return dict(index=i,table=table,status="ok",dfa=d,
                    states=len(states),edges=sum(map(len,edges)),
                    attempts=attempts)
    return dict(index=i,table=table,status="unresolved",attempts=attempts)

def main(outdir):
    out=Path(outdir);out.mkdir(parents=True,exist_ok=True)
    with ProcessPoolExecutor(max_workers=8) as pool:
        rows=list(pool.map(search_one,enumerate(TARGETS)))
    hits=[r for r in rows if r["status"]=="ok"]
    (out/"attempts.json").write_text(json.dumps(rows,indent=2)+"\n")
    bank=[{k:r[k] for k in ("table","status","dfa","states","edges")} for r in hits]
    (out/"bank.json").write_text(json.dumps(bank,separators=(",",":"))+"\n")
    src=["import BiDFA","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
         "namespace BB6.Agent46Raw13Coupled6GapSAT",
         "open BB6Coverage BB6Coverage.Agent16BiDFA"]
    for r in hits:
        code,n,e=emit(r["index"],r["table"],*r["dfa"])
        assert (n,e)==(r["states"],r["edges"])
        src.append(code)
    src += ["end BB6.Agent46Raw13Coupled6GapSAT",""]
    (out/"Raw13Coupled6GapSAT.lean").write_text("\n".join(src))
    for r in rows:
        print(r["table"],r["status"],r.get("states"),r.get("edges"),r["attempts"],flush=True)
    print("hits",len(hits),"of",len(TARGETS),flush=True)

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/a46-gap-sat")
