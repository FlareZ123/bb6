#!/usr/bin/env python3
"""Untrusted proposal generator for the delayed paired-clock certificate.
All cover transport and recoveries are checked by Lean's kernel.
"""
import argparse
from pathlib import Path

def lane4(b,s):
    x=(1<<b)-1
    for j in range(s): x |= x << (4*b*(1<<j))
    return x
def plan4(L):
    return [(3*(1<<k),lane4(1<<k,L-k)) for k in range(L-1,-1,-1)]
def digit(n,P,q):
    i=q-2*n-3
    return (P>>i)&1 if i>=0 else 0
def shift(n,P,r):
    return 2*digit(n,P,2*r+2)+digit(n,P,2*r+1)
def pair_back(plan,r,t,bits):
    for s,m in plan: bits=(bits|(bits<<s))&m
    u=bits<<t
    extra=((u>>(2*r))|(u>>(4*r+1)))&1
    return (u|(u>>r)|(u>>(2*r+1))|(u>>(3*r+1))|extra)&((1<<r)-1)
def unpack(bits):
    out=[]
    while bits:
        x=bits&-bits
        out.append(x.bit_length()-1)
        bits-=x
    return out
def packed(xs):
    return sum(1<<x for x in xs)
def pred(r,t,a):
    u=4*a+t
    return (u%(2*r+1))%r if u<4*r+2 else None

def recover(n,s,h,B,c):
    P=7*B
    z=c
    w=0
    for i in range(s+h-1,s-1,-1):
        q=n+i+3
        x,z=divmod(2*z+digit(n,P,q),q)
        w=(w<<1)+x
    return B+(w<<s),z

def reverse_cover(n,s,h,B,dense,sparse):
    F=2*n+s+3
    assert F%2==0 and (n+s+h+3)%2==0 and h<n
    R=F//2-1
    target=(n+s+h+3)//2
    L=R.bit_length()
    plan=plan4(L)
    bits=(1<<R)-1
    r=R
    dense_cp=[(r,bits)]
    while r>target and bits.bit_count()>256:
        d=min(dense,r-target)
        for _ in range(d):
            r-=1
            bits=pair_back(plan,r,shift(n,7*B,r),bits)
        dense_cp.append((r,bits))
    xs=unpack(bits)
    sparse_cp=[(r,xs)]
    P=7*B
    while r>target:
        d=min(sparse,r-target)
        for _ in range(d):
            r-=1
            t=shift(n,P,r)
            xs=sorted({v for x in xs if (v:=pred(r,t,x)) is not None})
        sparse_cp.append((r,xs))
    return F,L,dense_cp,sparse_cp

def write(directory,module,imports,ns,body):
    lines=[*(f'import {m}' for m in imports),f'namespace {ns}',
        'open BB6.Agent43LagPair BB6.Agent45.DelayedCarry BB6.Agent43P1Complement',
        'open BB6.Agent43LagCert',
        'set_option maxRecDepth 1000000','set_option maxHeartbeats 0',
        'set_option exponentiation.threshold 1000000',
        *body,f'end {ns}','']
    (directory/(module+'.lean')).write_text('\n'.join(lines),encoding='utf-8')

def name(i,j): return f'B{i}_{j}'
def fmtps(i,ps): return '['+', '.join(f'({name(i,j)},{a})' for j,(B,a) in enumerate(ps))+']'

def main(n,h,dense,sparse,group,directory):
    assert n%2==0 and h%2==0 and h<n and n>=8000
    directory.mkdir(parents=True,exist_ok=True)
    stages=[[(1,(n+2)//2)]]
    covers=[]
    s=1
    for i in range(12):
        stage=[]
        children=[]
        for j,(B,a) in enumerate(stages[-1]):
            F,L,dc,sc=reverse_cover(n,s,h,B,dense,sparse)
            r,xs=sc[-1]
            out=[]
            for x in xs:
                c=2*x+digit(n,7*B,2*r)
                C,b=recover(n,s,h,B,c)
                if b==a and C%4==1:
                    out.append((C,c))
            indexes=[]
            for p in out:
                if p not in children: children.append(p)
                indexes.append(children.index(p))
            stage.append((F,L,dc,sc,indexes))
            print(f'stage={i} parent={j} s={s} dense_chunks={len(dc)-1} sparse_chunks={len(sc)-1} midpoints={len(xs)} children={[(c,C.bit_length()) for C,c in out]}',flush=True)
        covers.append(stage)
        stages.append(children)
        if not children: break
        s+=h
    else: raise RuntimeError('not extinct in twelve windows')
    ns='BB6.Agent43LagCert'
    words=[]
    for i,ps in enumerate(stages):
        words += [f'def {name(i,j)} : Nat := {B:#x}' for j,(B,a) in enumerate(ps)]
        words += [f'def ps{i} : List Prefix := {fmtps(i,ps)}']
    write(directory,'LagCertWords',['LagPairSource'],ns,words)
    imports=[]
    for i,stage in enumerate(covers):
        s=1+i*h
        for j,(F,L,dc,sc,indexes) in enumerate(stage):
            p=f'P{i}_{j}'
            pns=ns+'.'+p
            B=name(i,j)
            a=stages[i][j][1]
            R=dc[0][0]
            body=[f'def cp0 : Nat := 2^{R}-1',
                  f'theorem c0 : Live {n} (7*{B}) {F} {R} (fun a=>cp0.testBit a=true) := live_start {n} (7*{B}) {F} {R}']
            prev='LagCertWords'
            shard=0
            count=0
            def flush():
                nonlocal body,prev,shard,count
                mod=f'LagCert{p}G{shard:04}'
                write(directory,mod,[prev],pns,body)
                prev=mod
                shard+=1
                count=0
                body=[]
            for k,(r,bits) in enumerate(dc[1:],1):
                old=dc[k-1][0]
                body += [f'def cp{k} : Nat := {bits:#x}',
                         f'theorem c{k} : Live {n} (7*{B}) {F} {r} (fun a=>cp{k}.testBit a=true) :=',
                         f'  dense_extend {L} {n} (7*{B}) {F} {old} {old-r} cp{k-1} cp{k} (by decide) (by decide) (by decide) c{k-1} (by decide +kernel)']
                count+=1
                if count>=group: flush()
            r,xs=sc[0]
            k=len(dc)-1
            body += [f'def xs0 : List Nat := {xs}',
                     f'theorem v0 : Live {n} (7*{B}) {F} {r} (·∈xs0) :=',
                     f'  dense_to_sparse {n} (7*{B}) {F} {r} cp{k} xs0 c{k} (by decide +kernel)']
            for k,(r,xs) in enumerate(sc[1:],1):
                old=sc[k-1][0]
                body += [f'def xs{k} : List Nat := {xs}',
                         f'theorem v{k} : Live {n} (7*{B}) {F} {r} (·∈xs{k}) :=',
                         f'  sparse_extend {n} (7*{B}) {F} {old} {old-r} xs{k-1} xs{k} (by decide) (by decide) v{k-1} (by decide +kernel)']
                count+=1
                if count>=group*4: flush()
            k=len(sc)-1
            r=sc[-1][0]
            out='['+', '.join(f'({name(i+1,l)},{stages[i+1][l][1]})' for l in indexes)+']'
            body += [f'theorem recover_eq : recoverList {n} {s} {h} {B} {a} (midpoints {n} (7*{B}) {r} xs{k}) = {out} := by decide +kernel',
                     f'theorem parent (C c : Nat) (ht : Trace {n} {s} {B} {a}) (hc : C%4=1)',
                     f'    (he : Extend {n} {s} {B} {a} {h} C c) (hsuf : ∃ D d, Extend {n} {s+h} C c {n-h} D d) : (C,c)∈ps{i+1} := by',
                     f'  apply parent_advance {n} {s} {h} {B} {a} C c {r} xs{k} ps{i+1} (by decide) (by decide) v{k} _ ht hc he hsuf',
                     '  intro p hp',
                     '  rw [recover_eq] at hp']
            if indexes:
                body += ['  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp',
                         '  rcases hp with '+'|'.join('rfl' for _ in indexes)]
                for l in indexes:
                    body += [f'  · unfold ps{i+1}', '    '+('apply List.mem_cons_of_mem\n    '*l)+'exact List.mem_cons_self']
            else:
                body+=['  simp at hp']
            flush()
            imports.append(prev)
    body=[f'theorem half0 : HalfCovered {n} 1 ps0 := half_start {n}']
    for i,ps in enumerate(stages[:-1]):
        s=1+i*h
        body += [f'theorem half{i+1} : HalfCovered {n} {s+h} ps{i+1} := by',
                 f'  apply half_advance {n} {s} {h} ps{i} ps{i+1} (by decide) (by decide) half{i}',
                 '  intro B a C c hp ht hc he hsuf',
                 f'  simp only [ps{i},List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp',
                 '  rcases hp with '+'|'.join('⟨rfl,rfl⟩' for _ in ps)]
        for j in range(len(ps)):
            body+=[f'  · exact P{i}_{j}.parent C c ht hc he hsuf']
    k=len(covers)
    s=1+k*h
    body+=[f'theorem critical_reset_no_reach_{n} : ¬ BB6.Agent1.Reach 2 (14*2^{n}-2*{n}-10) := by',
           f'  apply critical_empty_half {n} {s} (by decide) (by decide) (by decide) (by decide +kernel)',
           f'  exact half{k}',f'#print axioms critical_reset_no_reach_{n}']
    write(directory,'LagPairFinite',imports,ns,body)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--n',type=int,default=124834)
    p.add_argument('--h',type=int,default=62416)
    p.add_argument('--dense',type=int,default=128)
    p.add_argument('--sparse',type=int,default=512)
    p.add_argument('--group',type=int,default=2)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    main(a.n,a.h,a.dense,a.sparse,a.group,a.output)
