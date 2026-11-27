#!/usr/bin/env python3
"""Propose exact low/high-bit residue masks, verified by Lean checkRows/checkKeys.
The proposal is not trusted. Each row is checked independently.
"""
import argparse
from pathlib import Path
from collections import defaultdict


def expand(k, ps):
    P = 1 << k
    for r, a, B in ps:
        t = a % 2
        yield r + P*t, (a+t*B)//2, B
        C = a+r+3+k
        S = B+P
        t = C % 2
        yield r + P*t, (C+t*S)//2, S


def table(k, d):
    ps = [(0, 1, 1)]
    for i in range(1, k):
        ps = list(expand(i, ps))
    grouped = defaultdict(list)
    for p in ps:
        grouped[p[0] % (1 << k)].append(p)
    rows = []
    for r, qs in sorted(grouped.items()):
        for i in range(k, k+d):
            qs = list(expand(i, qs))
        mask = 0
        for R, a, B in qs:
            assert R % (1 << k) == r
            mask |= 1 << (R >> k)
        rows.append((r, mask))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('k', type=int)
    ap.add_argument('d', type=int)
    ap.add_argument('--group', type=int, default=1)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    k, d, group = args.k, args.d, args.group
    assert k>=1 and d>=0 and group>=1
    out=args.out
    out.mkdir(parents=True,exist_ok=True)
    rows=table(k,d)
    count=sum(m.bit_count() for r,m in rows)
    name=f'AffineFinite{k}_{d}'
    imports=[]
    for i in range(0,len(rows),group):
        j=i//group
        sub=f'{name}_Rows{j:04d}'
        imports.append(sub)
        data=',\n  '.join(f'({r}, 0x{m:x})' for r,m in rows[i:i+group])
        (out/(sub+'.lean')).write_text(f'''import AffineTable
namespace BB6.Agent9AffineResidue.{name}
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

def rows{j} : List (Nat×Nat) := [
  {data}]
theorem rows{j}_ok : checkRows {k} {d} rows{j}=true := by decide +kernel
end BB6.Agent9AffineResidue.{name}
''')
    n=len(imports)
    (out/(name+'.lean')).write_text(''.join(f'import {x}\n' for x in imports)+f'''namespace BB6.Agent9AffineResidue.{name}
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

def rows : List (Nat×Nat) := {' ++ '.join(f'rows{j}' for j in range(n))}
theorem rows_ok : checkRows {k} {d} rows=true := by
  simp only [rows,checkRows_append,{','.join(f'rows{j}_ok' for j in range(n))},Bool.and_self]
theorem keys_ok : checkKeys {k} rows=true := by decide +kernel

theorem mask_eq (r : Nat) : localMask {k} {d} r=lookup r rows := table_eq {k} {d} r rows rows_ok keys_ok

theorem count_exact : residueCount {k} {d}={count} := by
  rw [residueCount_eq {k} {d} rows rows_ok keys_ok]
  decide +kernel

theorem critical_reset_no_reach (n : Nat) (hn : {max(14,k+d)}≤n)
    (h : (lookup (n%2^{k}) rows).testBit ((n%2^{k+d})/2^{k})=false) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro hr
  have hm := critical_reset_requires_mask {k} {d} n (by decide) (by omega) (by omega) hr
  rw [mask_eq] at hm
  rw [h] at hm
  contradiction

#print axioms mask_eq
#print axioms count_exact
#print axioms critical_reset_no_reach
end BB6.Agent9AffineResidue.{name}
''')
    print(f'{name}: {len(rows)} rows, exact support proposal {count} out of {1<<(k+d)} residues, {count/(1<<(k+d-1)):.8%} of even residues')


if __name__=='__main__': main()
