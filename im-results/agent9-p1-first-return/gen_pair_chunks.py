#!/usr/bin/env python3
"""Untrusted proposal generator: paired exact-integer common-clock bitsets.
Every chunk and its numerical checkpoint are validated by the Lean kernel.
"""
import argparse
from pathlib import Path


def lane4(b: int, s: int) -> int:
    x = (1 << b)-1
    for j in range(s):
        x |= x << (4*b*(1 << j))
    return x


def spread_plan(L: int) -> list[tuple[int,int]]:
    return [(3*(1 << k), lane4(1 << k,L-k)) for k in range(L-1,-1,-1)]


def mask(r: int) -> int:
    return ((1 << (r-2))-1) << 1


def pair_back(plan: list[tuple[int,int]], r: int, bits: int) -> int:
    for s,m in plan:
        bits=(bits | (bits << s)) & m
    return (bits | (bits >> r) | (bits >> (2*r+1)) | (bits >> (3*r+1))) & mask(r)


def survivor(r: int, hi: int, bits: int) -> bool:
    return 2*r-4<=hi and (r-1)%2==0 and bool((bits >> ((r-1)//2)) & 1)


def proposal(lo: int, hi: int, block: int):
    assert 14<=lo<=hi and lo%2==0 and hi%2==0 and block>0
    R=lo+1
    assert hi+4<2*R
    L=R.bit_length()
    plan=spread_plan(L)
    r=R
    bits=mask(R)
    hits=[]
    checkpoints=[(r,bits)]
    while r>(lo+4)//2:
        for _ in range(min(block,r-(lo+4)//2)):
            r-=1
            bits=pair_back(plan,r,bits)
            if survivor(r,hi,bits): hits.append(2*r-4)
        checkpoints.append((r,bits))
    return R,L,sorted(hits),checkpoints


def write_module(directory: Path, module: str, imports: list[str], ns: str, body: list[str]):
    lines = [*(f'import {x}' for x in imports), f'namespace {ns}',
             'open BB6.Agent9PairCarry', 'set_option maxRecDepth 1000000',
             'set_option maxHeartbeats 0', *body, f'end {ns}', '']
    (directory / f'{module}.lean').write_text('\n'.join(lines),encoding='utf-8')


def chain(lo: int, hi: int, block: int, group: int, directory: Path):
    R,L,hits,cps=proposal(lo,hi,block)
    ns=f"BB6.Agent9PairCarry.C{lo}_{hi}"
    prefix=f"PairCert{lo}_{hi}_"
    body=[f'def skip : List Nat := {hits}', f'def cp0 : Nat := halfMask {R}',
          f'theorem pc0 : PairCertificate skip {R} {hi} {R} cp0 :=',
          f'  pairCert_start skip {R} {hi} (by decide)']
    prev='PairChunks'
    shard=0
    for i,(r,bits) in enumerate(cps[1:],1):
        start=cps[i-1][0]
        body += [f'def cp{i} : Nat := {bits:#x}',
                 f'theorem pc{i} : PairCertificate skip {R} {hi} {r} cp{i} :=',
                 f'  pairCert_extend {L} skip {R} {hi} {start} {start-r} cp{i-1} cp{i} (by decide) (by decide) (by decide) pc{i-1} (by decide +kernel)']
        if i%group==0:
            mod=f'{prefix}{shard:04}'
            write_module(directory,mod,[prev],ns,body)
            prev=mod; shard+=1; body=[]
    r,bits=cps[-1]
    i=len(cps)-1
    body += [f'theorem except_range :',
             f'    ∀ n, {lo}≤n → n≤{hi} → n%2=0 → n∉skip → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=',
             f'  pairCert_interval skip {R} {hi} {lo} {r} cp{i} (by decide) (by decide) (by decide) (by decide) pc{i}']
    mod=f'{prefix}{shard:04}'
    write_module(directory,mod,[prev],ns,body)
    print(f'lo={lo} hi={hi} F={2*R+1} chunks={i} shards={shard+1} final_width={bits.bit_count()} hits={hits}',flush=True)
    return mod,ns,hits


def make(lo: int, hi: int, block: int, group: int, output: Path):
    assert group>0
    output.parent.mkdir(parents=True,exist_ok=True)
    mod,ns,hits=chain(lo,hi,block,group,output.parent)
    imports=[mod]
    for n in hits:
        mod,_,remaining=chain(n,n,block,group,output.parent)
        if remaining: raise ValueError(f'full-horizon survivor {n}; no complete interval certificate')
        imports.append(mod)
    name=f'critical_reset_no_reach_chunks_{lo}_{hi}'
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
            body += [f'{prefix}exact C{n}_{n}.except_range {n} (by decide) (by decide) (by decide) (by decide)']
    body += [f'  · exact {ns}.except_range n hlo hhi he hm', f'#print axioms {name}']
    write_module(output.parent,output.stem,imports,'BB6.Agent9PairCarry',body)


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('lo',type=int)
    parser.add_argument('hi',type=int)
    parser.add_argument('--block',type=int,default=256)
    parser.add_argument('--group',type=int,default=4)
    parser.add_argument('--output',type=Path,default=Path('PairChunkFinite.lean'))
    a=parser.parse_args()
    make(a.lo,a.hi,a.block,a.group,a.output)
