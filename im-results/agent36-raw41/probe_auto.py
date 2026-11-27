#!/usr/bin/env python3
"""Construct candidate Agent46 symbolic sweep proof for hard Raw41 leaves.

A found candidate is a single-source Lean AutoPump fixture, not a proof
until Agent46AutoPump.check and its soundness are compiled by the kernel.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"im-results/agent46-raw13-cut"))
from autoword import infer,Word

TWO_HARD={
 8:"1RB1LB_1RC0RC_0RD0LE_1LD1RA_0LF---_1RB1LF",
 14:"1RB1LB_1RC0RC_0RD0LE_1LD1RA_1LC1LF_0LD---",
}

def word(w:Word):
    return w.pre if not w.block else [w.pre,w.block,word(w.post)]

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--leaf",type=int,required=True)
    a.add_argument("--table",type=str,default=None,help="Exact optional one-hole table (use instead of built-in child084 pair)")
    a.add_argument("--seconds",type=int,default=45)
    a.add_argument("--out",type=Path,required=True)
    x=a.parse_args()
    table=x.table or TWO_HARD[x.leaf]
    assert len(table.replace("_",""))==36
    print(f"Raw41 child084 leaf{x.leaf}: {table}",flush=True)
    import time
    start=time.monotonic()
    result=infer(table.replace("_",""),limit=20000,budget=x.seconds)
    elapsed=time.monotonic()-start
    x.out.parent.mkdir(parents=True,exist_ok=True)
    if not result or result[0]=="hole":
        x.out.write_text(json.dumps({"leaf":x.leaf,"found":False,
                    "seconds":elapsed,"search_result":repr(result)})+"\n")
        print(f"NO_AUTO_CANDIDATE leaf{x.leaf}: {repr(result)}",flush=True)
        return
    entry,f,(inc,path,(aa,bb)),end=result
    ops=[]
    for _,_,info in path:
        if info is None:
            if ops and isinstance(ops[-1],int):ops[-1]+=1
            else:ops.append(1)
        else:
            d,lp,rp,I,O,k,L,R=info
            if d=="L":lp,rp,L,R=rp,lp,R,L
            ops.append([d,lp,rp,I,O,word(L),word(R),k])
    fixture={"table":table,"entry":entry,"family":[f.q,word(f.l),word(f.r)],
      "inc":inc,"ops":ops,"a":aa,"b":bb}
    x.out.write_text(json.dumps({"leaf":x.leaf,"found":True,
       "seconds":elapsed,"end":end,"fixture":fixture},indent=2)+"\n")
    print(f"AUTO_CANDIDATE leaf{x.leaf} entry={entry} inc={inc} "
          f"a={aa} b={bb} ops={len(ops)}",flush=True)
if __name__=="__main__":
    main()
