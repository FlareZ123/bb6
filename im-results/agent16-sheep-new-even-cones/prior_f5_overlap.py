#!/usr/bin/env python3
"""Independent exact F-depth-five overlap test for new Sheep E families."""
from functools import lru_cache
from hashlib import sha256
from math import gcd
from sympy.ntheory import n_order

OLD_MOD=5400
CASES=((118,14580),(246,24300),(558,8100),(846,8100),(702,11340))

@lru_cache(None)
def period(m):
    p=1 if m==1 else int(n_order(2,m))
    assert pow(2,p,m)==1%m
    return p

def valcut(f):
    s,b,d=f
    a=0
    while True:
        K=d*(2*a-1)-2*b
        if 1<K<(1<<a) and (1<<a)>=2*d:
            return a
        a+=1

def exceptional_threshold(f):
    shift,b,d=f
    h=(3*d).bit_length()-1-shift
    assert h>=0
    L=3*d-(1<<(shift+h))
    U=(1<<(shift+h+1))-3*d
    assert L>0 and U>0
    j=max(5,h+1)
    while True:
        q=1<<j
        if (L*q > (1<<h)*b and
            U*q > (1<<(h+1))*(d*(j+3)-b) and
            U*q > (1<<(h+1))*d):
            return j
        j+=1

@lru_cache(None)
def vals(f,r):
    s,b,d=f
    assert exceptional_threshold(f)<=100
    assert (1<<(100+s))+b>5*d
    available=[]
    for a in range(valcut(f)):
        m=d*((1<<(a+1))+1)
        q=period(m)//gcd(period(m),OLD_MOD)
        assert pow(2,OLD_MOD*q,m)==1%m
        K=d*(2*a-1)-2*b
        if any(pow(2,r+s+1+OLD_MOD*k,m)==K%m for k in range(q)):
            available.append(a)
    return tuple(available)

@lru_cache(None)
def closes(f,r,depth):
    available=vals(f,r)
    if not available:return True
    if depth==0:return False
    s,b,d=f
    return all(closes((s+a+1,(1<<(a+1))*b+(1<<a)*d*(1-2*a),d*((1<<(a+1))+1)),r,depth-1) for a in available)

def main():
    entire=[r for r in range(OLD_MOD) if closes((0,0,1),r,5)]
    digest=sha256(','.join(map(str,entire)).encode('ascii')).hexdigest()
    assert len(entire)==3596 and digest=='dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b'
    print('PASS reproduced 3596/5400 exact prior F-depth-five residues and SHA256',digest)
    for J,P in CASES:
        R=sorted({(J+P*k)%OLD_MOD for k in range(OLD_MOD//gcd(P,OLD_MOD))})
        excluded=[r for r in R if r in entire]
        assert excluded==[],(J,excluded)
        print('PASS disjoint',J,P,'projected F5 residues',R)

if __name__=='__main__': main()
