#!/usr/bin/env python3
"""Exact ideal-seam counts and rigorous entropy-tail enclosure (paper theorem)."""
from collections import defaultdict
from fractions import Fraction as F
import argparse

def counts(M):
    levels=defaultdict(list)
    levels[0]=[1]
    pow3=[3**a for a in range(M+1)]
    out=[]
    for A in range(M+1):
        den=pow3[A]
        q=levels.pop(A,[])
        n=0
        while q:
            p=q.pop()
            n+=1
            # Same-level even inverse, excluding the seam self-loop.
            if A and 4*p>3*den:
                q.append(2*p-den)
            for a in range(1,M-A+1):
                d=pow3[A+a]
                # j >= a+2: odd crossings strictly lower the level.
                j=max(a+2,(3*d//(2*p)).bit_length()-1)
                while 2*(p<<j)<=3*d:
                    j+=1
                if p<<j<2*d:
                    levels[A+a].append((p<<j)-d)
        out.append(n)
    return out

def geometric_tail(start):
    r=F(8,9)
    t,odd=divmod(start,2)
    if not odd:
        return F(27,14)*(1+r)*r**(3*t)/(1-r**3)
    return F(27,14)*(r**(3*t+1)+(1+r)*r**(3*t+3)/(1-r**3))

def enclosure(M,L):
    assert 1<=M<=L
    ns=counts(M)
    lo=1+sum(F(3*n,2*3**a) for a,n in enumerate(ns) if a)
    c=(1,1,1)
    S=[1]
    for _ in range((3**L).bit_length()-1):
        x,y,z=c
        c=x+y,z,z+x
        S.append(c[0])
    hi=lo+sum(F(3*S[(3**a).bit_length()-1],2*3**a) for a in range(M+1,L+1))+geometric_tail(L+1)
    return ns,lo,hi

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--valuation',type=int,default=24)
    parser.add_argument('--tail-cutoff',type=int,default=256)
    args=parser.parse_args()
    ns,lo,hi=enclosure(args.valuation,args.tail_cutoff)
    print('counts',ns)
    scale=10**8
    # Exact outward rounding, no floating-point claim.
    lower=lo.numerator*scale//lo.denominator
    upper=-(-hi.numerator*scale//hi.denominator)
    print('c_inf in [',F(lower,scale),',',F(upper,scale),']')
    if args.valuation==24 and args.tail_cutoff==256:
        assert lo>F(151902529,10**8)
        assert hi<F(1551323,10**6)
