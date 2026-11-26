#!/usr/bin/env python3
"""Recompute and emit the twenty 0LF run-length quotient witnesses."""
from pathlib import Path
from generate_rf_run_quotients import run_search, quotient, edge_count, emit
ROOT=Path(__file__).resolve().parent
def generate(rows,out):
    for line in (ROOT/"zeroLF-run-quotients.txt").read_text().splitlines():
        x,y,z=line.split(":")
        i,*params=map(int,x.split())
        raw,small=tuple(map(int,y.split())),tuple(map(int,z.split()))
        table=rows[i]
        D,n,info=run_search(table,params)
        assert D is not None,(i,n,info)
        E,S=info
        assert (n,len(D[0])//2,len(D[1])//2,edge_count(E))==raw,i
        record=quotient(table,D,E,S)
        assert (record["states"],len(record["dfa"][0])//2,len(record["dfa"][1])//2,record["edges"])==small,i
        emit(out,f"Raw54ZeroLFRun{i}",record)
if __name__=="__main__":
    out=ROOT/"cold-generated"
    generate((out/"0LF/miss.txt").read_text().splitlines(),out)
