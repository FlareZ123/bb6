#!/usr/bin/env python3
"""Exact finite reset-scan quotient and independent primitive witness checks."""
from itertools import product
from collections import Counter

def step(p,n):
    a,e,f,ze,zf=p
    one=(a,e,f); zero=(None,ze,zf)
    s,r=1,0
    for _ in range(n):
        c=one[s];s=c//2;r=r+1 if c%2 else 0
    if s==0:return 'h',n+1
    c=zero[s];d=one[c//2];s=d//2
    cs=[c,d]
    for _ in range(2):
        if s==0:break
        c=zero[s];cs.append(c);s=c//2
    if s!=0:return 'd',0
    for c in cs:r=r+1 if c%2 else 0
    return 'n',(r,n+len(cs)+r+4)

def cls(n):return n if n<8 else 8+(n-8)%6

def outcome(p):
    n,t=0,4;seen=set()
    while cls(n) not in seen:
        seen.add(cls(n));k,x=step(p,n)
        if k=='h':return 'h',t+x
        if k=='d':return 'd',None
        n,dt=x;t+=dt
    return 'c',None

def row(p,b=0):
    a,e,f,ze,zf=([2,4,18,20,22,24][i] for i in p)
    return (8,a,11,b,11,13,18,15,ze,e,zf,f)

def sim(p,n):
    tab=row(p);q=0;x=0;tape=set()
    for i in range(n+1):
        v=tab[2*q+(x in tape)]
        if v==0:return i
        z=v-1
        if z//2%2:tape.add(x)
        else:tape.discard(x)
        x+=1 if z%2 else -1;q=z//4
    return None

def main():
    hist=Counter();counts=Counter();best=[];comparisons=0
    for p in product(range(6),repeat=5):
        k,t=outcome(p);counts[k]+=1
        if k=='h':
            hist[t]+=1;best.append((t,p))
            assert sim(p,t)==t,(p,t)
        for n in range(8,14):
            for j in (1,3,10):
                a,b=step(p,n),step(p,n+6*j)
                assert a[0]==b[0] and (a[0]!='n' or cls(a[1][0])==cls(b[1][0]))
                comparisons+=1
    assert counts=={'c':3764,'d':2989,'h':1023}
    assert max(hist)==50
    maxima=[p for t,p in best if t==50]
    assert maxima==[(3,5,0,1,1),(5,0,3,1,1)]
    print(counts,sorted(hist.items()),maxima)
    print('Verified',len(best),'primitive halt witnesses;',comparisons,'finite period comparisons')
if __name__=='__main__':main()
