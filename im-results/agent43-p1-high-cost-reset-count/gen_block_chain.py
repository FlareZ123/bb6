#!/usr/bin/env python3
"""Generate independent Lean kernel-checkable block certificates for P1.
Usage: python gen_block_chain.py N K WIDTH GROUP OUTPUT_DIR
Each group generates untrusted literal lists in Lean; all transitions and
margins are verified by decide +kernel. Build modules in modules.txt order.
"""
import sys
from pathlib import Path

def generate(n,K,H,G,out):
    assert n>=14 and K>1 and 1<=H<=10 and G>0
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    stem=f'BlockMargin{n}';ns=f'BB6.Agent43Block.{stem}'
    opts=['set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option exponentiation.threshold 10000']
    base=stem+'Base'
    (out/(base+'.lean')).write_text('\n'.join(['import BlockProposal',f'namespace {ns}','open BB6.Agent43CarryCert',*opts,f'def q : Nat := 7*2^{n}-({n}+3)',f'def l : Nat := requiredMargin {n} {K}',f'end {ns}'])+'\n')
    layers=[0,1]+list(range(1+H,K,H))+[K]
    modules=[base];groups=[]
    for idx,start in enumerate(range(0,len(layers)-1,G)):
        chunk=layers[start:start+G+1];a,z=chunk[0],chunk[-1]
        mod=stem+f'G{idx}'; gns=f'{ns}.G{idx}'
        lines=[f'import {base}',f'namespace {gns}', 'open BB6.Agent43CarryCert',*opts]
        lines += [f'carry_literal layer{a} := proposeAt q {H} {a}']
        for p,j in zip(chunk,chunk[1:]):
            h=j-p
            if j==K: lines += [f'def layer{j} : List Nat := []']
            else: lines += [f'carry_block layer{j} := q {p} {h} layer{p}']
            if p==0:
                rhs=f'cover_single q l 0 layer0 layer{j} (by decide +kernel) (by decide +kernel)'
            else:
                rhs=f'cover_block q l {p} {h} layer{p} layer{j} (by decide +kernel) (by decide +kernel) (by decide +kernel)'
            lines += [f'private theorem seg{j} : Cover q l {p} layer{p} {h} layer{j} := {rhs}']
            rhs=f'seg{j}' if p==a else f'@Cover.append q l {a} {p-a} {h} layer{a} layer{p} layer{j} prefix{p} seg{j}'
            lines += [f'{"theorem" if j==z else "private theorem"} prefix{j} : Cover q l {a} layer{a} {j-a} layer{j} := {rhs}']
        lines += [f'end {gns}']
        (out/(mod+'.lean')).write_text('\n'.join(lines)+'\n');modules.append(mod);groups.append((mod,a,z,idx))
    # A balanced proof-composition tree avoids a giant linear defeq chain.
    aggregate=[f'import {mod}' for mod,_,_,_ in groups]+[f'namespace {ns}','open BB6.Agent43CarryCert',*opts]
    def merge(i,j):
        if i==j:
            _,a,z,idx=groups[i]
            return f'G{idx}.prefix{z}',a,z,f'G{idx}.layer{a}',f'G{idx}.layer{z}'
        m=(i+j)//2
        left,a,b,la,lb=merge(i,m);right,_,z,rb,rz=merge(m+1,j)
        name=f'join{i}_{j}'
        # This type conversion checks the independently generated shared boundary.
        aggregate.append(f'private theorem {name} : Cover q l {a} {la} {z-a} {rz} :=\n  @Cover.append q l {a} {b-a} {z-b} {la} {lb} {rz} {left} {right}')
        return name,a,z,la,rz
    name,_,_,_,_=merge(0,len(groups)-1)
    aggregate += [f'theorem margin{n} : MarginSafe (7*2^{n}-({n}+3)) (requiredMargin {n} {K}) 0 [1] {K} [] := Cover.toMargin {name}',f'#print axioms margin{n}',f'end {ns}']
    (out/(stem+'.lean')).write_text('\n'.join(aggregate)+'\n');modules.append(stem)
    (out/(stem+'Source.lean')).write_text('\n'.join([f'import {stem}','import MarginSource',f'namespace {ns}','open BB6.Agent43MarginSource',f'theorem critical_reset_no_reach_{n} : ¬ BB6.Agent1.Reach 2 (14*2^{n}-2*{n}-10) :=',f'  critical_reset_no_reach_of_margin {n} {K} (by decide) (by decide) margin{n}',f'#print axioms critical_reset_no_reach_{n}',f'end {ns}'])+'\n')
    (out/'modules.txt').write_text('\n'.join(modules)+'\n')
    print(f'n={n}, K={K}, width={H}, {len(layers)-1} blocks, {len(groups)} independent groups')

if __name__=='__main__':
    generate(*map(int,sys.argv[1:5]),sys.argv[5])
