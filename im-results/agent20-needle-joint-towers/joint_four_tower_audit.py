#!/usr/bin/env python3
"""Independent exact finite regression of four joint deep Needle inverse arms.

For every k=1,...,6, construct a *single* cancellation feeder index
satisfying the 19/67/131/4099 fixed-point depth-k congruences together
with the fifth immediate 35-congruence; no floating point or libraries.
Finite audit is not the all-k Hensel/CRT proof in FOUR-DEEP-ARMS.md.
"""
from math import gcd
PRIMES={3:19,5:67,6:131,11:4099}
ORD2={3:18,5:66,6:130,11:4098}

def geometric(x,y,n,m):
    if n==0:return 0
    if n==1:return 1
    h=geometric(x,y,n//2,m)
    even=h*(pow(x,n//2,m)+pow(y,n//2,m))%m
    return even if n%2==0 else (x*even+pow(y,n-1,m))%m

def feeder(r,p,k,ord2):
    m=p**k;order=ord2*p**(k-1)
    a=((pow(9,r,2*order)+5)//2)%order
    A=pow(2,a,m)
    return pow(2,(a-1)%order,m)*(A-3)*geometric(A*A%m,9,r,m)%m

def fixed_target(w,k):
    p=PRIMES[w]
    return -2**w*(2*w-3)*pow(3,-1,p**k)%p**k

def lift(w,base,period,k):
    p=PRIMES[w]
    for depth in range(1,k):
        t=period*p**(depth-1)
        m=p**(depth+1)
        slope={3:12,5:23,6:390*pow(9,base,131),11:2144}[w]%p
        assert slope
        assert feeder(base,p,depth,ORD2[w])==fixed_target(w,depth)
        assert (feeder(base+t,p,depth+1,ORD2[w])-feeder(base,p,depth+1,ORD2[w]))%m==slope*p**depth
        delta=(fixed_target(w,depth+1)-feeder(base,p,depth+1,ORD2[w]))%m
        assert delta%p**depth==0
        digit=delta//p**depth*pow(slope,-1,p)%p
        base+=digit*t
        assert feeder(base,p,depth+1,ORD2[w])==fixed_target(w,depth+1)
    return base,period*p**(k-1)

def crt(a,m,b,n):
    g=gcd(m,n)
    assert (b-a)%g==0,(a,m,b,n,g)
    nn=n//g
    t=((b-a)//g*pow(m//g,-1,nn))%nn if nn>1 else 0
    return (a+m*t)%(m*nn),m*nn

Q=35697042810
R=4152608179
for k in range(1,7):
    classes=[
        lift(3,7,9,k),lift(5,49,165,k),
        lift(6,12979,51090,k),lift(11,R,Q,k)
    ]
    r,period=classes[-1]
    for x,m in classes[:-1]:r,period=crt(r,period,x,m)
    if r==0:r=period
    for w in [3,5,6,11]:
        assert feeder(r,PRIMES[w],k,ORD2[w])==fixed_target(w,k)
    assert feeder(r,35,1,12)==20
    assert period==Q*(19*67*131*4099)**(k-1)
    print(f'k={k} index={r} period={period}')
print('PASS: one prepared feeder, four independent depth-k arms plus fifth first parent')
