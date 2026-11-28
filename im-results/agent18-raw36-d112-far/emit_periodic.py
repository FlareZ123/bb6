"""Exact repeated-word and block-language witnesses; independent Lean closure checker."""
from functools import lru_cache
from collections import defaultdict
from pathlib import Path
import json,sys
from emit_trace_learn import parse,load,generate
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'agent4-two-sided-automata'))
from quotient import compress

def mkpush(periods,repeat,mod,maxbits=128):
    specs=[]
    for p in periods:
        k=repeat+mod;mask=(1<<p)-1;full=(1<<(p*k))-1
        specs.append((p,mask,full,full//mask,p*mod,p*k))
    @lru_cache(maxsize=50000)
    def f(x,b):
        z=x*2+b
        for p,mask,full,factor,drop,length in specs:
            if z.bit_length()>=length and z&full == (z&mask)*factor:
                z >>= drop
                break
        if z.bit_length()>maxbits:raise ValueError('growth')
        return z
    return f

def blockpush(k,delay,mode):
    @lru_cache(maxsize=20000)
    def f(x,b):
        if x==0:return (1,1,0,0,0) if b else 0
        n,s,phase,seen,z=x;s=(s<<1)|b;n+=1
        if n>delay+k:
            a=(s>>(n-k))&((1<<k)-1);n-=k;s&=(1<<n)-1
            assert mode==0
            seen|=1<<a;phase=(phase+1)%2
        return n,s,phase,seen,z
    return f

def gram_push(k,delay,mod,mode):
    @lru_cache(maxsize=30000)
    def f(x,b):
        if x==0:return (1,1,0,0) if b else 0
        n,s,phase,seen=x;s=(s<<1)|b;n+=1
        if n>delay+k:
            a=s>>(n-k);n-=1;s&=(1<<n)-1
            assert mode==1
            seen|=1<<(phase*(k+1)+a.bit_count());phase=(phase+1)%mod
        return n,s,phase,seen
    return f

def check(p,lp,rp,cap=150000):
    f=[lp,rp];T=[[0],[0]];ids=[{0:0},{0:0}];D=[{},{}];E=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)]
    for e in E:e[0].add((0,0))
    seen={(0,0,0,0)};todo=list(seen)
    def add(z):
        if z not in seen:
            if p[2*z[0]+z[1]]=='---':raise ValueError('hole')
            seen.add(z);todo.append(z)
            if len(todo)>cap:raise ValueError('cap')
    def pop(z,e,j):
        q,a,l,r=z;b,k=e;m=p[2*q+a];s=ord(m[2])-65
        add((s,b,j,k) if m[1]=='R' else (s,b,k,j))
    for z in todo:
        q,a,l,r=z;m=p[2*q+a];w=int(m[0]);d=int(m[1]=='L');x=(l,r)[d];y=(l,r)[1-d]
        if (x,w) not in D[d]:
            state=f[d](T[d][x],w)
            if state not in ids[d]:ids[d][state]=len(T[d]);T[d].append(state)
            D[d][x,w]=ids[d][state]
        j=D[d][x,w];e=(w,x)
        if e not in E[d][j]:
            E[d][j].add(e)
            for zz,k in wait[d][j]:pop(zz,e,k)
        wait[1-d][y].append((z,j))
        for e in E[1-d][y]:pop(z,e,j)
    return len(seen),*[ [D[d].get((k,b),0) for k in range(len(T[d])) for b in (0,1)] for d in (0,1)]

def main(out):
    old=load('remaining74.txt','d60bcc1439f1a933e2fbbf5677c3771eb834ab8a53e297f8d4985f7afc601340').decode().splitlines()
    rem=load('remaining48.txt','e5d19697d18d57280ff8547f3191caa7216f58de9a80742062e13aaa6b41e80a').decode().splitlines()
    specs=json.loads((HERE/'periodic_specs.json').read_text())
    found=set()
    for name,stem in [('pump','Raw36D112Pump'),('phase','Raw36D112Phase'),('phase2','Raw36D112Phase2')]:
        rows=[]
        for i,s,expected in specs[name]:
            t=old[i];assert t in rem and t not in found;found.add(t)
            f=mkpush(*s) if name=='pump' else (blockpush(*s[1:]) if s[0]=='b' else gram_push(*s[1:]))
            n,l,r=check(parse(t),f,f);assert n==expected,(i,n,expected)
            rows.append([i,t,n,l,r])
        generate(rows,out,stem,chunk=2,compressor=compress)
    assert len(found)==47
    residual=set(rem)-found
    assert residual=={old[41]}
    (Path(out)/'remaining1.txt').write_text(old[41]+'\n')
    print('Generated 47 source-checkable exact witnesses; remaining:',old[41])

if __name__=='__main__':main(sys.argv[1])
