#!/usr/bin/env python3
"""Finite adversarial check; the full theorem is proved in PeriodicRunNoGo.md."""
from math import gcd
from itertools import combinations

def primitive(x):
    return all(x != x[:k]*(len(x)//k) for k in range(1,len(x)) if len(x)%k==0)

def types(gaps, initial):
    v=initial
    out=[]
    for j in gaps:
        out.append(v)
        if j%2: v='S' if v=='E' else 'E'
    return out,v

def main(max_t=17):
    checked=0
    min_margin=10**30
    for t in range(2,max_t+1):
        mod=4**t-1
        for a in range(1,t):
            for positions in combinations(range(1,t),a-1):
                ones=(0,)+positions
                gaps=tuple((ones[(i+1)%a]-ones[i])%t or t for i in range(a))
                if not primitive(gaps):continue
                digits=[0]*t
                for pos in ones:digits[pos]=1
                p=0
                for digit in digits:p=4*p+digit
                q=mod//gcd(p,mod)
                assert q%2==1 and q>=6*t+1
                for initial in 'ES':
                    seq,end=types(gaps,initial)
                    if end==initial:full_types,J=seq,t
                    else:full_types,J=seq+types(gaps,end)[0],2*t
                    C=6*(J-len(full_types))+10*full_types.count('E')+14*full_types.count('S')
                    assert C%4==0
                    K=C//4
                    assert q>K,(t,gaps,seq,q,K)
                    min_margin=min(min_margin,q-K)
                    checked+=1
    print('PASS: typed cycles',checked,'minimum q-K',min_margin)

if __name__=='__main__':main()
