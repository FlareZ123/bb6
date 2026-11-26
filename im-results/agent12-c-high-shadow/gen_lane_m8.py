#!/usr/bin/env python3
"""Generate kernel-checkable counted paths for the genuine M8 prefix.
The independent literal sweep replay also checks each arithmetic edge and clock.
"""
import argparse
from pathlib import Path
from gen_bit_event_cutoff import State, transition

def macro(s):
    a,k,c=s.a,s.k,0
    out=[]
    while True:
        start=(a,k,c)
        h=0
        if c==0:
            if a==0:a,k,c,w=1,0,2*k+2,2*k+3
            elif a==1 and k==0:a,k,c,w=5,0,1,11
            elif a==1:a,k,c,w=2,2,2*k-1,2*k+16
            else:a,k,c,w=a-2,1,2*k+1,2*k+4
        elif c==1:a,k,c,w=a,k+1,0,2
        elif c==2:raise RuntimeError('unexpected halt')
        elif c==3:a,k,c,w=a,k+2,1,12
        elif a:
            h=min(a,c-3)
            w=2*h*h+(4*k+7)*h
            a,k,c=a-h,k+h,c-h
        elif k%2:a,k,c,w=2*k+3,0,c,5*k+13
        else:a,k,c,w=2*k+2,2,c-3,5*k+21
        out.append((start,(a,k,c),h or 1,w,h))
        if c==0:return State(a,k),sum(x[2] for x in out),sum(x[3] for x in out),out

def polynomial(s,t,r):
    a,M,x,o=s.a,s.mass,t.a,s.mass%2
    w=-4*a*a+16*a*o-22*a+4*M*M-4*M*x-8*M*o+24*M*r-M+4*x*x-8*x*o-12*x*r+11*x-96*o*r+96*o+36*r*r-51*r+39
    assert w%6==0
    return 2*s.k+r+o*(3-3*r),w//6

def tr(s):return f'({s.a},{s.k},0)'
def triple(p):return '('+','.join(map(str,p))+')'

HEAD='''import LanePathSource
import CRawCountBridge
open BB6.Agent47ThinCounted
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent12LaneM8
'''

def ordinary(i,s,t,N,q,K,T,W):
    return f'''private def q{i} : Nat := {hex(q)}
private def s{i} : BB6.Agent12WordBlock.State := {s.lean}
private def t{i} : BB6.Agent12WordBlock.State := {t.lean}
private def v{i} := BB6.Agent12LaneGenerator.recover s{i} t{i} {N} q{i}
private def w{i} := BB6.Agent12LaneClockSource.recoverAligned s{i} t{i} {N} q{i}
private theorem hc{i} : BB6.Agent12LaneCertificate.checked5 s{i} t{i} {N} q{i} {K} v{i} := by decide +kernel
private theorem ha{i} : BB6.Agent12LaneClock.alignmentChecked {N} q{i} v{i} w{i} := by decide +kernel
private theorem ct{i} : BB6.Agent12PlaneSum.sumTerms {N} q{i} (BB6.Agent12LaneClock.callsTerms {N} w{i}) = ({T}:Int) := by decide +kernel
private theorem cw{i} : BB6.Agent12PlaneSum.sumTerms {N} q{i} (BB6.Agent12LaneClock.weightTerms {N} w{i}) = ({6*W}:Int) := by decide +kernel
private theorem e{i} : Path {T} {W} {tr(s)} {tr(t)} := by
  obtain ⟨T',W',hp,ht,hw⟩ := BB6.Agent12LanePathSource.source_path5_and_bitplane_clock_of_checked5 q{i} {N} {K} v{i} w{i} s{i} t{i} hc{i} ha{i}
  rw [ct{i}] at ht
  rw [cw{i}] at hw
  have hT : T' = {T} := by omega
  have hW : W' = {W} := by omega
  change Path T' W' {tr(s)} {tr(t)} at hp
  rwa [hT,hW] at hp
'''

def exceptional(i,s,t,T,W,steps):
    lines=[]
    for j,(p,z,n,w,h) in enumerate(steps):
        target=f'private theorem ex{i}_{j} : Path {n} {w} {triple(p)} {triple(z)} := by'
        if h:
            proof=f'  exact BB6.Agent12CountedOrdinary.sweep_counted {h} {z[0]} {p[1]} {z[2]} (by decide)'
        else:
            proof=f'  exact Path.cons (by decide : BB6CLine.nextC {triple(p)} = some {triple(z)}) (Path.nil _)'
        lines.extend((target,proof))
    term=f'ex{i}_0'
    for j in range(1,len(steps)):term=f'Path.append ({term}) ex{i}_{j}'
    lines.append(f'private theorem e{i} : Path {T} {W} {tr(s)} {tr(t)} := {term}')
    return '\n'.join(lines)+'\n'

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--returns',type=int,default=150052)
    p.add_argument('--bits',type=int,default=2048)
    p.add_argument('--outdir',type=Path,default=Path(__file__).parent)
    args=p.parse_args()
    assert args.returns>0 and args.bits>0
    s=State(5,1);start=s
    q=N=K=T=W=0
    totalT=1;totalW=2
    blocks=exceptions=ordinary_returns=0
    lines=[HEAD,'private theorem ep0 : Path 1 2 (5,0,1) (5,1,0) := by exact Path.cons (by decide : BB6CLine.nextC (5,0,1) = some (5,1,0)) (Path.nil _)\n']
    def add(code,end,t,w):
        nonlocal blocks,totalT,totalW
        lines.append(code)
        totalT+=t;totalW+=w
        lines.append(f'private theorem ep{blocks+1} : Path {totalT} {totalW} (5,0,1) {tr(end)} := Path.append ep{blocks} e{blocks}\n')
        blocks+=1
    def flush():
        nonlocal q,N,K,T,W,start
        if K:add(ordinary(blocks,start,s,N,q,K,T,W),s,T,W)
        q=N=K=T=W=0;start=s
    for i in range(args.returns):
        r,t=transition(s)
        target,ct,cw,steps=macro(s)
        assert target==t,(i,s,target,t)
        if r is not None and s.a>=2 and s.k>=1 and t.k>=5:
            assert polynomial(s,t,r)==(ct,cw),(i,s,t,r,ct,cw)
            if N+r>args.bits:flush()
            q=(q<<r)|1;N+=r;K+=1;T+=ct;W+=cw
            ordinary_returns+=1
        else:
            flush()
            add(exceptional(blocks,s,t,ct,cw,steps),t,ct,cw)
            print('exception',i,s,t,ct,cw,len(steps))
            exceptions+=1;start=t
        s=t
    flush()
    lines.append(f'''theorem endpoint : Path {totalT} {totalW} (5,0,1) {tr(s)} := ep{blocks}
theorem blank_raw_endpoint : ∃ h, BB6Coverage.run BB6.Agent47CRaw.cMachine {totalW+12} BB6Coverage.blank = some (BB6.Agent47CRaw.embed h (BB6.Agent47CRaw.enc {tr(s)})) := BB6.Agent47CRaw.raw_blank_path endpoint
#print axioms endpoint
#print axioms blank_raw_endpoint
end BB6.Agent12LaneM8
''')
    args.outdir.mkdir(parents=True,exist_ok=True)
    (args.outdir/'LaneM8Generated.lean').write_text(''.join(lines))
    print('FINAL',args.returns,s,'ordinary',ordinary_returns,'exceptions',exceptions,'blocks',blocks,'calls',totalT,'moves',totalW+12)
    if args.returns==150052:
        assert (s,totalT,totalW+12,ordinary_returns,exceptions)==(State(621619,213453),39210104828,18269855715225886,150045,7)

if __name__=='__main__':main()
