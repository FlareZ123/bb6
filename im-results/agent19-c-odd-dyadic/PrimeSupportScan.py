"""Exact finite-support necessary-condition census for C=211 ordinary periodic shadows.

Uses full-lift imbalance theorem: if q=q0*m and ord_q(2)=m*ord_q0(2),
then delta=ell-b/2 is unchanged and m divides delta for admissible periods.
Only nonzero deltas need checking (balanced words excluded in ShadowPeriodicity.md).
"""
from itertools import product
import argparse
import math
import json

C=211

def primes_upto(n):
    ps=[]
    for x in range(3,n+1,2):
        if all(x%p for p in ps if p*p<=x):
            ps.append(x)
    return ps

def factors(n):
    p=2
    while p*p<=n:
        if n%p==0:
            yield p
            while n%p==0: n//=p
        p+=1
    if n>1: yield n

def order_prime(p):
    b=p-1
    for r in factors(b):
        while b%r==0 and pow(2,b//r,p)==1: b//=r
    return b

def lift_exponent(p,b):
    e,mod=1,p*p
    while pow(2,b,mod)==1:
        e+=1;mod*=p
    return e

def supports(ps):
    orders={p:order_prime(p) for p in ps}
    def visit(i, support, radical, b):
        yield support,b
        for z in range(i,len(ps)):
            p=ps[z]
            bb=math.lcm(b,orders[p]);qq=radical*p
            if qq<422*bb:
                yield from visit(z+1,support+(p,),qq,bb)
    yield from visit(0,(C,),C,210)

def smooth(ps, bound):
    if not ps:
        yield 1
        return
    p,*rest=ps
    x=1
    while x<=bound:
        for a in smooth(rest,bound//x): yield x*a
        x*=p

def possible_deltas(q0,b0,saturated):
    """Map each nonzero admissible base imbalance to lift multipliers."""
    out={}
    for m in smooth(saturated,(b0-1)//2):
        q=q0*m;b=b0*m
        h=(pow(2,b,C*q)-1)//q
        k0=5*h%C
        if k0%2: k0+=C
        if k0==0:k0=2*C
        for k in range(k0,844,2*C):
            delta=m*(k*(q0//C)-7*(b0//2))
            if 0<abs(delta)<b0//2:
                out.setdefault(delta,[]).append((m,k,h))
    return out

def orbit_check(q,b,targets):
    if pow(2,b//2,q)==q-1:return [],0
    seen=bytearray(q)
    hits=[];count=0
    for a in range(1,q):
        if seen[a] or math.gcd(a,q)!=1:continue
        x=a;ell=0;length=0
        while True:
            seen[x]=1
            xx=x*2
            if xx>=q:ell+=1;xx-=q
            x=xx;length+=1
            if x==a:break
        assert length==b
        count+=1
        delta=ell-b//2
        if delta in targets:
            hits.append((a,delta,targets[delta]))
    return hits,count

def scan(limit,orbit_limit):
    ps=[p for p in primes_upto(limit) if p!=C]
    stats=dict(limit=limit,supports=0,base_moduli=0,prefiltered=0,orbits=0,balanced_bases=0,passed=[],unexamined=[])
    for support,b0 in supports(ps):
        stats['supports']+=1
        es=[lift_exponent(p,b0) for p in support]
        for fs in product(*(range(1,e+1) for e in es)):
            q0=math.prod(p**f for p,f in zip(support,fs))
            if q0>=422*b0:continue
            stats['base_moduli']+=1
            sat=[p for p,f,e in zip(support,fs,es) if f==e]
            targets=possible_deltas(q0,b0,sat)
            if not targets:continue
            stats['prefiltered']+=1
            if pow(2,b0//2,q0)==q0-1:
                stats['balanced_bases']+=1;continue
            if q0>orbit_limit:
                stats['unexamined'].append((q0,b0,targets));continue
            hits,count=orbit_check(q0,b0,targets)
            stats['orbits']+=count
            for a,delta,ls in hits:
                for m,k,h in ls:stats['passed'].append(dict(q=q0*m,b=b0*m,base=q0,a=a,delta=delta,k=k,h=h))
    return stats

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--prime-limit',type=int,default=47)
    ap.add_argument('--orbit-limit',type=int,default=10_000_000)
    args=ap.parse_args()
    print(json.dumps(scan(args.prime_limit,args.orbit_limit),indent=2))
