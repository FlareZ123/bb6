#!/usr/bin/env python3
"""Generate sparse block proof checkpoints; the scalar generator is untrusted.
Each exact checkpoint is replayed by the kernel, and the initial packed
prelude is independently certified against the source semantics.
"""
import argparse
from pathlib import Path

def backward(q, xs):
    return sorted({r for z in xs if 1 <= (r := 2*z % q) <= q-3})

def make(lo, hi, prelude, k, work, block, arithmetic_only=False):
    F=2*lo+3; L=F.bit_length(); q=F
    assert 14<=lo<=hi and hi+4+prelude<F and prelude>0 and 2**(k+2)<=lo+4 and k>0 and work>0 and block>0
    xs=list(range(1,F-2))
    for _ in range(prelude):
        q-=1; xs=backward(q,xs)
    top=q; lines=['import '+('BirthBatch' if arithmetic_only else 'BirthSource'), 'namespace BB6.Agent45ReverseBlock', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0',f'def bcp0 : List Nat := {xs}']
    if not arithmetic_only:
        lines += [f'theorem bver0 : BlockVerified {F} {hi} {top} {q} bcp0 :=',f'  block_packed_start {L} {F} {hi} {q} {prelude} bcp0 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)']
    i=0; visits=0; filtered=0
    while q>lo+4:
        start=q; d=0; w=0; step=min(k,q-lo-4)
        while q>=lo+4+step and d<block and (w<work or d==0):
            w+=len(xs); visits+=len(xs)
            filtered+=sum((2**(step+1)*z)%q>q-2**(step+2) for z in xs)
            for _ in range(step):
                if q%2==0 and q-4<=hi and (q-2)//2 in xs: raise ValueError(f'survivor {q-4}')
                q-=1; xs=backward(q,xs)
            if q%2==0 and q-4<=hi and (q-2)//2 in xs: raise ValueError(f'survivor {q-4}')
            d+=1
        i+=1
        lines += [f'def bcp{i} : List Nat := {xs}',f'theorem bcheck{i} : advanceMany {hi} {step} {start} bcp{i-1} {d}=(true,bcp{i}) := by decide +kernel']
        if not arithmetic_only:
            lines += [f'theorem bver{i} : BlockVerified {F} {hi} {top} {q} bcp{i} :=',f'  verified_many {F} {hi} {top} {start} {step} {d} bcp{i-1} bcp{i} (by decide) (by decide) (by decide) bver{i-1} bcheck{i}']
    if not arithmetic_only:
        lines += [f'theorem critical_reset_no_reach_{lo}_{hi} :',f'  ∀ n, {lo}≤n → n≤{hi} → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=',f'  block_verified_interval {F} {hi} {top} {lo} {q} bcp{i} (by decide) (by decide) (by decide) (by decide) (by decide) bver{i}',f'#print axioms critical_reset_no_reach_{lo}_{hi}']
    lines += ['end BB6.Agent45ReverseBlock','']
    print(f'F={F} top={top} chunks={i} final_width={len(xs)} block_endpoint_visits={visits} window_hits={filtered}')
    return '\n'.join(lines)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('lo',type=int);p.add_argument('hi',type=int);p.add_argument('--prelude',type=int,default=512);p.add_argument('--k',type=int,default=6);p.add_argument('--work',type=int,default=512);p.add_argument('--block',type=int,default=64);p.add_argument('--arithmetic-only',action='store_true');p.add_argument('--output',type=Path,default=Path('BirthFinite.lean'));a=p.parse_args();a.output.write_text(make(a.lo,a.hi,a.prelude,a.k,a.work,a.block,a.arithmetic_only),encoding='utf8')
