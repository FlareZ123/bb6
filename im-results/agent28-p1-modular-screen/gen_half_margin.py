#!/usr/bin/env python3
"""Generate untrusted reflected-carry certificate layers and independent Lean shards."""
import sys
from pathlib import Path

def generate(n, K, block, group, out):
    assert n>=14 and n%2==0 and K>1 and block>0 and group>0
    out=Path(out); out.mkdir(parents=True,exist_ok=True)
    Q=7*2**n-n-3; L=2*(n+3*K+10)+6
    cs=[(Q+1)//2]; layers=[(1,cs)]
    for j in range(1,K):
        assert all(p>=L for p in cs), (n,j)
        B=Q+2-j
        nxt=[]
        for p in cs:
            if p%2==0: nxt.append(p//2)
            if (B-p)%2==0 and (p%2!=0 or p!=B-p): nxt.append((B-p)//2)
        cs=nxt
        if j%block==0 or j+1==K: layers.append((j+1,cs))
    assert not cs
    stem=f'HalfMargin{n}'; ns=f'BB6.Agent28HalfCarry.{stem}'
    opts=['set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option exponentiation.threshold 10000']
    def write(name,lines): (out/(name+'.lean')).write_text('\n'.join(lines)+'\n')
    def literal(xs): return '['+','.join(hex(x) for x in xs)+']'
    base=stem+'Base'; modules=[base]; data_names=[]; groups=[]
    write(base,['import HalfCarry',f'namespace {ns}',*opts,
        f'def q : Nat := 7*2^{n}-({n}+3)',f'def l : Nat := BB6.Agent43CarryCert.requiredMargin {n} {K}',
        'def layer1 : List Nat := [(q+1)/2]',f'end {ns}'])
    for idx,start in enumerate(range(0,len(layers)-1,group)):
        chunk=layers[start:start+group+1]; a=chunk[0][0]; z=chunk[-1][0]
        name=f'{stem}G{idx}'; data=name+'Data'; data_names.append(data)
        write(data,[f'import {base}',f'namespace {ns}',*opts,
            *[f'def layer{j} : List Nat := {literal(xs)}' for j,xs in chunk[1:]],f'end {ns}'])
        lines=[f'import {data}']
        if idx: lines.append(f'import {data_names[idx-1]}')
        lines += [f'namespace {ns}',*opts]
        for i in range(1,len(chunk)):
            p,r=chunk[i-1][0],chunk[i][0]; length=r-p
            lines += [f'private theorem seg{r} : HalfSafe q l {p} layer{p} {length} layer{r} :=',
                f'  half_sound q l {p} layer{p} layer{r} {length} (by decide +kernel)']
            rhs=f'seg{r}' if i==1 else f'@HalfSafe.append q l {a} {p-a} {length} layer{a} layer{p} layer{r} local{p} seg{r}'
            lines += [f'{"theorem" if r==z else "private theorem"} local{r} : HalfSafe q l {a} layer{a} {r-a} layer{r} :=',f'  {rhs}']
        lines += [f'end {ns}']; write(name,lines)
        groups.append((name,a,z)); modules += [data,name]
    # The proof modules are independent. Only the final module loads all shards.
    lines=[f'import {name}' for name,_,_ in groups]+[f'namespace {ns}',*opts]
    prev=None
    for name,a,z in groups:
        rhs=f'local{z}' if prev is None else f'@HalfSafe.append q l 1 {a-1} {z-a} layer1 layer{a} layer{z} prefix{a} local{z}'
        lines += [f'private theorem prefix{z} : HalfSafe q l 1 layer1 {z-1} layer{z} :=',f'  {rhs}']
        prev=z
    lines += [f'theorem margin{n} : BB6.Agent43CarryCert.MarginSafe q l 0 [1] {K} [] :=',
        f'  margin_of_half q l {K} (by decide +kernel) (by decide +kernel) (by decide +kernel) prefix{K}',
        f'#print axioms margin{n}',f'end {ns}']
    write(stem,lines); modules.append(stem)
    write(stem+'Source',[f'import {stem}','import MarginSource',f'namespace {ns}',
        *opts,'open BB6.Agent43MarginSource',
        f'theorem critical_reset_no_reach_{n} : ¬ BB6.Agent1.Reach 2 (14*2^{n}-2*{n}-10) :=',
        f'  critical_reset_no_reach_of_margin {n} {K} (by decide) (by decide) margin{n}',
        f'#print axioms critical_reset_no_reach_{n}',f'end {ns}'])
    (out/'modules.txt').write_text('\n'.join(modules)+'\n')
    print(f'n={n}, K={K}, {len(layers)-1} segments, {len(groups)} independent groups',flush=True)

if __name__=='__main__':
    n,K,block,group=map(int,sys.argv[1:5]); generate(n,K,block,group,sys.argv[5])
