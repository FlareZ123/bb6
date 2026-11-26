#!/usr/bin/env python3
"""Replay all 23 0LF exact growth recipes using existing arbitrary-tail proofs."""
from pathlib import Path
from la_multivar import C, Machine, gen
from generate_rf_growth import replay
ROOT = Path(__file__).resolve().parent
def emit_growth(rows, out):
    for line in (ROOT/"zeroLF-growth.txt").read_text().splitlines():
        i,entry,q,l,r,ps,tl,tr,a,b=line.split()
        i,entry,a,b=map(int,(i,entry,a,b))
        l,r,tl,tr=map(lambda s: "" if s=="-" else s,(l,r,tl,tr))
        ps=tuple(ps.split(","))
        st,tg=C(q,l,r,ps),C(q,tl,tr,ps)
        m=Machine(rows[i])
        ans=replay(m,st,tg,a,b)
        assert ans is not None and ans[1]==(a,b),i
        source=gen(i,m,st,tg,entry,ans).replace("BB6.Agent8Raw54.LA.","BB6.Agent8Raw54.ZeroLF.").replace("maxHeartbeats 1000000","maxHeartbeats 0")
        (out/f"Raw54ZeroLFGrow{i}.lean").write_text(source)
if __name__=="__main__":
    out=ROOT/"cold-generated"
    emit_growth((out/"0LF/miss.txt").read_text().splitlines(),out)
