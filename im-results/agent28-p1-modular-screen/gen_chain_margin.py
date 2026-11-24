#!/usr/bin/env python3
"""Untrusted generator of small independent kernel-checked P1 carry certificates.
Every generated segment is checked by margin_sound; shared boundary definitions
and explicit composition avoid elaborating a large recursively unfolded state list.
Usage: python gen_chain_margin.py N K BLOCK GROUP OUTPUT_DIR
Compile the modules in modules.txt order with LEAN_PATH including the generated directory.
"""
import sys
from pathlib import Path

def generate(n, K, block, group, out):
    assert n >= 14 and K > 0 and block > 0 and group > 0
    out = Path(out); out.mkdir(parents=True, exist_ok=True)
    Q = 7 * 2**n - (n+3)
    L = 2 * (n+3*K+10) + 6
    cs = [1]
    layers = [(0,cs)]
    for j in range(K):
        assert all(c != 2 and c+L+j <= Q+2 for c in cs), (n,j)
        cs = [v//2 for c in cs for v in (c,c+Q-j) if v%2 == 0]
        if (j+1)%block == 0 or j+1 == K: layers.append((j+1,cs))
    assert not cs
    stem = f'ChainMargin{n}'; ns = f'BB6.Agent43CarryCert.{stem}'
    opts = ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option exponentiation.threshold 10000']
    def literal(cs): return '[' + ','.join(hex(c) for c in cs) + ']'
    modules=[]
    base = stem+'Base'
    (out/(base+'.lean')).write_text('\n'.join(['import MarginCert',f'namespace {ns}',*opts,
        f'def q : Nat := 7*2^{n}-({n}+3)',f'def l : Nat := requiredMargin {n} {K}',
        'def layer0 : List Nat := [1]',f'end {ns}'])+'\n')
    modules.append(base)
    groups=[]
    for idx,start in enumerate(range(0,len(layers)-1,group)):
        chunk = layers[start:start+group+1]; a=chunk[0][0]; z=chunk[-1][0]
        name=f'{stem}G{idx}'; data=name+'Data'
        lines=[f'import {base}',f'namespace {ns}',*opts]
        for j,cs in chunk[1:]: lines.append(f'def layer{j} : List Nat := {literal(cs)}')
        lines.append(f'end {ns}')
        (out/(data+'.lean')).write_text('\n'.join(lines)+'\n')
        modules.append(data)
        lines=[f'import {data}']
        if idx: lines.append(f'import {groups[-1][0]}')
        lines += [f'namespace {ns}',*opts]
        for s in range(1,len(chunk)):
            j0,j1=chunk[s-1][0],chunk[s][0]; b=j1-j0
            lines.append(f'private theorem seg{j1} : MarginSafe q l {j0} layer{j0} {b} layer{j1} :=\n  margin_sound q l {j0} layer{j0} layer{j1} {b} (by decide +kernel)')
            if s==1 and not idx: rhs=f'seg{j1}'
            else: rhs=f'@MarginSafe.append q l 0 {j0} {b} layer0 layer{j0} layer{j1} prefix{j0} seg{j1}'
            lines.append(f'{"theorem" if j1==z else "private theorem"} prefix{j1} : MarginSafe q l 0 layer0 {j1} layer{j1} :=\n  {rhs}')
        if z==K:
            lines += [f'theorem margin{n} : MarginSafe (7*2^{n}-({n}+3)) (requiredMargin {n} {K}) 0 [1] {K} [] := prefix{K}',f'#print axioms margin{n}']
        lines.append(f'end {ns}')
        (out/(name+'.lean')).write_text('\n'.join(lines)+'\n')
        modules.append(name);groups.append((name,a,z))
    (out/(stem+'.lean')).write_text(f'import {groups[-1][0]}\n')
    modules.append(stem)
    (out/'modules.txt').write_text('\n'.join(modules)+'\n')
    print(f'n={n}, K={K}, {len(layers)-1} segments, {len(groups)} groups')

if __name__ == '__main__':
    n,K,block,group=map(int,sys.argv[1:5]);generate(n,K,block,group,sys.argv[5])
