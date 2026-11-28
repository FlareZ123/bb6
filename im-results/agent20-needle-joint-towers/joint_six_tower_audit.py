#!/usr/bin/env python3
"""Six simultaneous depth-k Space Needle reverse branches plus seventh parent.

Exact original cancellation finite polynomial; six prime-power Hensel lifts,
generalized CRT, and one independent valuation-four source congruence.
Finite k<=5 audit, not a replacement for the all-k proof in SIX-DEEP-ARMS.md.
"""
from math import gcd
Q=35697042810
R=4152608179
CASES=[
    (3,19,18,7,9,12),
    (5,67,66,49,165,23),
    (6,131,130,12979,51090,None),
    (11,4099,4098,R,Q,2144),
    (14,32771,32770,R+Q*7824,Q*91756,14966),
    (17,262147,262146,R+Q*2976,Q*190885979,227076),
]

def geometric(x,y,n,m):
    if n==0:return 0
    if n==1:return 1
    half=geometric(x,y,n//2,m)
    even=half*(pow(x,n//2,m)+pow(y,n//2,m))%m
    return even if n%2==0 else (x*even+pow(y,n-1,m))%m

def feeder(r,p,k,ord2):
    m=p**k
    order=ord2*p**(k-1)
    a=((pow(9,r,2*order)+5)//2)%order
    A=pow(2,a,m)
    return pow(2,(a-1)%order,m)*(A-3)*geometric(A*A%m,9,r,m)%m

def target(w,p,k):
    return -2**w*(2*w-3)*pow(3,-1,p**k)%p**k

def lift(w,p,ord2,r,period,slope,k):
    for depth in range(1,k):
        step=period*p**(depth-1)
        m=p**(depth+1)
        delta_s=(slope if slope is not None else 390*pow(9,r,131))%p
        assert delta_s!=0
        assert feeder(r,p,depth,ord2)==target(w,p,depth)
        assert (feeder(r+step,p,depth+1,ord2)-feeder(r,p,depth+1,ord2))%m==delta_s*p**depth
        needed=(target(w,p,depth+1)-feeder(r,p,depth+1,ord2))%m
        assert needed%p**depth==0
        digit=(needed//p**depth)*pow(delta_s,-1,p)%p
        r+=digit*step
        assert feeder(r,p,depth+1,ord2)==target(w,p,depth+1)
    return r,period*p**(k-1)

def crt(a,m,b,n):
    g=gcd(m,n)
    assert (b-a)%g==0,(a,m,b,n,g)
    nn=n//g
    t=(b-a)//g*pow(m//g,-1,nn)%nn if nn>1 else 0
    return (a+m*t)%(m*nn),m*nn

BASE=Q*91756*190885979
MULT=19*67*131*4099*32771*262147
for k in range(1,6):
    classes=[lift(*case,k) for case in CASES]
    r,period=classes[-1]
    for a,m in classes[:-1]:
        r,period=crt(r,period,a,m)
    if r==0:r=period
    for w,p,o,_,_,_ in CASES:
        assert feeder(r,p,k,o)==target(w,p,k)
    assert feeder(r,35,1,12)==20
    assert period==BASE*MULT**(k-1)
    print(f'k={k} index={r} period={period}')
print('PASS: six deep prepared branches plus seventh first parent for every sampled depth')
