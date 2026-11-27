#!/usr/bin/env python3
"""Propose hybrid packed/sparse interval certificates. All data is untrusted;
   each checkpoint equality and original-source transfer is kernel-checked."""
from __future__ import annotations
import argparse
from pathlib import Path
from gen_pair_chunks import mask, spread_plan, pair_back, survivor, write_module


def unpack(bits: int) -> list[int]:
    out=[]
    while bits:
        b=bits & -bits
        out.append(b.bit_length()-1)
        bits-=b
    return out


def sparse_back(r: int, xs: list[int]) -> list[int]:
    # Exactly the four disjoint intervals used by pairSparseBack. Each branch
    # is sorted and duplicate-free if the supplied checkpoint was so.
    vals=set()
    for a in xs:
        v=4*a
        for off in (0,r,2*r+1,3*r+1):
            if off+1<=v and v+2<=off+r:
                vals.add(v-off)
    return sorted(vals)


def proposal(lo: int, hi: int, block: int, threshold: int, work: int):
    assert 14<=lo<=hi and lo%2==0 and hi%2==0 and block>0 and threshold>0 and work>0
    R=lo+1
    assert hi+4<2*R
    L=R.bit_length()
    plan=spread_plan(L)
    r=R; bits=mask(R); hits=[]
    dense=[(r,bits)]; bottom=(lo+4)//2
    while r>bottom and bits.bit_count()>threshold:
        for _ in range(min(block,r-bottom)):
            r-=1; bits=pair_back(plan,r,bits)
            if survivor(r,hi,bits): hits.append(2*r-4)
        dense.append((r,bits))
    xs=unpack(bits); sparse=[(r,xs)]; visits=0
    while r>bottom:
        chunk=0; j=0
        while r>bottom and (j==0 or chunk+max(1,len(xs))<=work) and j<1024:
            chunk+=max(1,len(xs)); j+=1; r-=1
            xs=sparse_back(r,xs)
            if 2*r-4<=hi and (r-1)%2==0 and (r-1)//2 in xs: hits.append(2*r-4)
        visits+=chunk; sparse.append((r,xs))
    return R,L,sorted(hits),dense,sparse,visits


def chain(lo: int, hi: int, block: int, group: int, threshold: int, work: int, directory: Path):
    R,L,hits,dense,sparse,visits=proposal(lo,hi,block,threshold,work)
    ns=f'BB6.Agent9PairCarry.S{lo}_{hi}'; prefix=f'PairSparse{lo}_{hi}_'
    body=[f'def skip : List Nat := {hits}', f'def cp0 : Nat := halfMask {R}',
          f'theorem pc0 : PairCertificate skip {R} {hi} {R} cp0 :=',
          f'  pairCert_start skip {R} {hi} (by decide)']
    prev='PairSparse'; shard=0; count=0
    def flush():
        nonlocal prev,shard,count,body
        mod=f'{prefix}{shard:04}'
        write_module(directory,mod,[prev],ns,body)
        prev=mod; shard+=1; count=0; body=[]
    for i,(r,bits) in enumerate(dense[1:],1):
        start=dense[i-1][0]
        body += [f'def cp{i} : Nat := {bits:#x}',
                 f'theorem pc{i} : PairCertificate skip {R} {hi} {r} cp{i} :=',
                 f'  pairCert_extend {L} skip {R} {hi} {start} {start-r} cp{i-1} cp{i} (by decide) (by decide) (by decide) pc{i-1} (by decide +kernel)']
        count+=1
        if count==group: flush()
    if count: flush()
    r,xs=sparse[0]
    body += [f'def sp0 : List Nat := {xs}',
             f'theorem sc0 : PairSparseCertificate skip {R} {hi} {r} sp0 :=',
             f'  pairSparse_convert skip {R} {hi} {r} cp{len(dense)-1} sp0 pc{len(dense)-1} (by decide +kernel)']
    count=1
    for i,(r,xs) in enumerate(sparse[1:],1):
        start=sparse[i-1][0]
        body += [f'def sp{i} : List Nat := {xs}',
                 f'theorem sc{i} : PairSparseCertificate skip {R} {hi} {r} sp{i} :=',
                 f'  pairSparse_extend skip {R} {hi} {start} {start-r} sp{i-1} sp{i} (by decide) (by decide) sc{i-1} (by decide +kernel)']
        count+=1
        if count==group: flush()
    r,xs=sparse[-1]
    i=len(sparse)-1
    body += [f'theorem except_range :',
             f'    ∀ n, {lo}≤n → n≤{hi} → n%2=0 → n∉skip → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=',
             f'  pairSparse_interval skip {R} {hi} {lo} {r} sp{i} (by decide) (by decide) (by decide) (by decide) sc{i}']
    flush()
    print(f'lo={lo} hi={hi} F={2*R+1} dense={len(dense)-1} sparse={i} shards={shard} switch_width={len(sparse[0][1])} visits={visits} final_width={len(xs)} hits={hits}',flush=True)
    return prev,ns,hits


def make(lo: int, hi: int, block: int, group: int, threshold: int, work: int, output: Path):
    assert group>0
    output.parent.mkdir(parents=True,exist_ok=True)
    mod,ns,hits=chain(lo,hi,block,group,threshold,work,output.parent)
    imports=[mod]
    for n in hits:
        mod,_,remaining=chain(n,n,block,group,threshold,work,output.parent)
        if remaining: raise ValueError(f'full-horizon survivor {n}; no complete interval certificate')
        imports.append(mod)
    name=f'critical_reset_no_reach_sparse_{lo}_{hi}'
    body=[f'theorem {name} :',
          f'    ∀ n, {lo}≤n → n≤{hi} → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by',
          '  intro n hlo hhi he',
          f'  by_cases hm : n∈{ns}.skip',
          f'  · simp [{ns}.skip] at hm']
    if hits:
        if len(hits)>1: body += ['    rcases hm with '+ '|'.join('rfl' for _ in hits)]
        else: body += ['    subst n']
        for n in hits:
            prefix='    · ' if len(hits)>1 else '    '
            body += [f'{prefix}exact S{n}_{n}.except_range {n} (by decide) (by decide) (by decide) (by decide)']
    body += [f'  · exact {ns}.except_range n hlo hhi he hm', f'#print axioms {name}']
    write_module(output.parent,output.stem,imports,'BB6.Agent9PairCarry',body)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('lo',type=int); p.add_argument('hi',type=int)
    p.add_argument('--block',type=int,default=128)
    p.add_argument('--group',type=int,default=2)
    p.add_argument('--threshold',type=int,default=512)
    p.add_argument('--work',type=int,default=5000)
    p.add_argument('--output',type=Path,default=Path('PairSparseFinite.lean'))
    a=p.parse_args(); make(a.lo,a.hi,a.block,a.group,a.threshold,a.work,a.output)
