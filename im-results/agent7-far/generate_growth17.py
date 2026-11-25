"""Reproduce 17 exact affine-growth candidate certificates; Lean checks all equations."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"agent10-tnf-multipump"))
import multi
ROWS = [
('1RB1RE1RC1LF0RD1RA1LD1RE0LE0LB---0LA',9,0,(),(('010',False),('010010',True),('1',False)),36,32),
('1RB0RF1RC1LF0RD1RA1LD1RE---0LB1LA0LA',9,0,(),(('01',False),('111111',True),('01',False)),68,80),
('1RB0LD1RC1LF0RD1RB1LD1RE1LE0LB---0LA',9,0,(),(('0101',False),('0101',True)),19,10),
('1RB---1RC1LF0RD1LC1LD1RE1RC0LB0RF0LA',25,2,(('111011',False),('1111',True)),(),57,20),
('1RB---1RC1LF0RD1LC1LD1RE0RE0LB0RF0LA',27,2,(('011011',False),('11',True)),(),35,10),
('1RB1LA1RC1LF0RD1RC1LD1RE1RB0LB---0LA',30,0,(),(('111',False),('11',True),('010101',False)),22,4),
('1RB1LA1RC1LF0RD1RC1LD1RE0LE0LB---0LA',26,0,(),(('11',False),('1',True),('0101',False),('1',True)),22,2),
('1RB1LA1RC1LF0RD1RC1LD1RE1LF0LB---0LA',30,0,(),(('1111',False),('1111',True),('0101',False)),32,8),
('1RB1RD1RC1LF0RD1RC1LD1RE1LF0LB---0LA',9,0,(),(('0101',False),('0101',True)),29,20),
('1RB1LE1RC1LF0RD1RC1LD1RE1LF0LB---0LA',9,0,(),(('0101',False),('0101',True)),21,12),
('1RB1LF1RC1LF0RD1RC1LD1RE1LF0LB---0LA',9,0,(),(('0101',False),('0101',True)),21,12),
('1RB0LC1RC1LF0RD0RE1LD1RE1RA0LB---0LA',34,0,(),(('01011',False),('1',True),('0101',False)),23,4),
('1RB1LE1RC1LF0RD1RE1LD1RE1RC0LB---0LA',9,0,(),(('0101',False),('0101',True)),17,8),
('1RB0RB1RC1LF0RD0LF1LD1RE---0LB0RF0LA',9,0,(),(('0101',False),('11',True)),57,34),
('1RB1LE1RC1LF0RD0RF1LD1RE---0LB0LA0LA',9,0,(),(('0101',False),('0101',True)),21,12),
('1RB1RF1RC1LF0RD0RF1LD1RE---0LB0RE0LA',9,0,(),(('0101',False),('11',True)),33,42),
('1RB1LE1RC1LF0RD1RF1LD1RE---0LB1RC0LA',9,0,(),(('0101',False),('0101',True)),17,8),
]
def advance(w):
    return multi.clean(sum((multi.lit(s)+multi.rep(s) if b else multi.lit(s) for s,b in w),()))
def main():
    out=["import SweepPumping","set_option maxHeartbeats 0","set_option maxRecDepth 100000","namespace BB6.Agent7DepthEightGrowth17","open BB6Coverage BB6Coverage.Agent31Pump"]
    for i,(code,t,q,l,r,a,b) in enumerate(ROWS,1):
        p=multi.parse(code)
        st=multi.C(q,l,r)
        tg=multi.C(q,advance(l),advance(r))
        ans=multi.pump(p,st,tg,limit=1200)
        assert ans is not None, (i,code)
        hist,_=ans
        assert (sum(x[3] for x in hist if x[0]=='step'),sum(x[3] for x in hist if x[0]=='loop'))==(a,b), (i,hist)
        proof,info=multi.generate(i,p,(t,st,tg,ans))
        out.append(proof)
        print(i,info)
    out.append("end BB6.Agent7DepthEightGrowth17")
    Path(__file__).with_name("DepthEightGrowth17.lean").write_text("\n\n".join(out)+"\n")
if __name__=="__main__":
    main()
