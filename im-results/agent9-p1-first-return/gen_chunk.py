#!/usr/bin/env python3
"""Generate composable exact Lean reverse-sweep certificates. No verdict is
trusted until the generated source passes decide +kernel and the source bridge.
"""
import argparse
from pathlib import Path


def backward(q: int, xs: list[int]) -> list[int]:
    return sorted({p for z in xs if 1 <= (p := (2*z)%q) <= q-3})


def make(lo: int, hi: int, prelude: int, work: int, block: int) -> str:
    F = 2*lo+3
    L = F.bit_length()
    assert 14 <= lo <= hi and hi+4+prelude < F
    assert prelude > 0 and work > 0 and block > 0
    q = F
    xs = list(range(1,F-2))
    for _ in range(prelude):
        q -= 1
        xs = backward(q,xs)
    top = q
    lines = ['import BatchCarryChunks','namespace BB6.Agent9BatchCarry',
        'set_option maxRecDepth 1000000','set_option maxHeartbeats 0',
        f'def cp0 : List Nat := {xs}',
        f'theorem ver0 : Verified {F} {hi} {top} {q} cp0 :=',
        f'  packed_start {L} {F} {hi} {q} {prelude} cp0 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)']
    i = 0
    while q > lo+4:
        start = q
        w = 0
        while q > lo+4 and q > start-block and (w < work or q == start):
            w += len(xs)
            q -= 1
            xs = backward(q,xs)
            if q%2 == 0 and q-4 <= hi and (q-2)//2 in xs:
                raise ValueError(f'survivor {q-4}')
        i += 1
        lines += [f'def cp{i} : List Nat := {xs}',
            f'theorem ver{i} : Verified {F} {hi} {top} {q} cp{i} :=',
            f'  extend_block {F} {hi} {top} {start} {start-q} cp{i-1} cp{i} (by decide) (by decide) (by decide) ver{i-1} (by decide +kernel)']
    lines += [f'theorem critical_reset_no_reach_{lo}_{hi} :',
        f'    ∀ n, {lo}≤n → n≤{hi} → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=',
        f'  verified_interval {F} {hi} {top} {lo} {q} cp{i} (by decide) (by decide) (by decide) (by decide) (by decide) ver{i}',
        f'#print axioms critical_reset_no_reach_{lo}_{hi}', 'end BB6.Agent9BatchCarry','']
    print(f'F={F} q_start={top} chunks={i} final_width={len(xs)}')
    return '\n'.join(lines)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('lo',type=int)
    parser.add_argument('hi',type=int)
    parser.add_argument('--prelude',type=int,default=128)
    parser.add_argument('--work',type=int,default=4000)
    parser.add_argument('--block',type=int,default=256)
    parser.add_argument('--output',type=Path,default=Path('ChunkFinite.lean'))
    args = parser.parse_args()
    args.output.write_text(make(args.lo,args.hi,args.prelude,args.work,args.block),encoding='utf-8')
