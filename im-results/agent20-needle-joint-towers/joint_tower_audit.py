#!/usr/bin/env python3
"""Exact arithmetic CRT for common v=3/5/6 depth k and v=4/11 one-step feeders.

Independent re-evaluation of the cancellation polynomial modulo each
denominator power. This script checks the finite instances, not the infinite
Hensel and CRT induction in README.md.
"""
from math import gcd

def geo(x,y,n,m):
    if n==0:return 0
    if n==1:return 1
    h=geo(x,y,n//2,m)
    v=h*(pow(x,n//2,m)+pow(y,n//2,m))%m
    return v if n%2==0 else (x*v+pow(y,n-1,m))%m

def B(r,p,k,order2):
    m=p**k; order=order2*p**(k-1)
    a=((pow(9,r,2*order)+5)//2)%order
    A=pow(2,a,m)
    return pow(2,(a-1)%order,m)*(A-3)*geo(A*A%m,9,r,m)%m

def crt(a,m,b,n):
    g=gcd(m,n)
    assert (b-a)%g==0
    nn=n//g
    z=((b-a)//g*pow(m//g,-1,nn))%nn if nn>1 else 0
    return (a+m*z)%(m*nn),m*nn

def target(p,w,k):
    return -2**w*(2*w-3)*pow(3,-1,p**k)%p**k

def lift(p,ord2,period_base,base_r,slope_fn,w,k):
    r=base_r
    for d in range(1,k):
        period=period_base*p**(d-1)
        m=p**(d+1)
        slope=slope_fn(r)%p
        assert slope!=0
        assert B(r,d,ord2=ord2,p=p)==target(p,w,d)
        assert (B(r+period,p,d+1,ord2)-B(r,p,d+1,ord2))%m==slope*p**d
        diff=(target(p,w,d+1)-B(r,p,d+1,ord2))%m
        assert diff%p**d==0
        r+=period*(diff//p**d*pow(slope,-1,p)%p)
        assert B(r,p,d+1,ord2)==target(p,w,d+1)
    return r,period_base*p**(k-1)

def full_lift(p,ord2,period_base,base_r,slope_fn,w,k):
    r=base_r
    for d in range(1,k):
        t=period_base*p**(d-1)
        m=p**(d+1)
        slope=slope_fn(r)%p
        assert slope!=0
        assert B(r,p,d,ord2)==target(p,w,d)
        assert (B(r+t,p,d+1,ord2)-B(r,p,d+1,ord2))%m==slope*p**d
        delta=(target(p,w,d+1)-B(r,p,d+1,ord2))%m
        assert delta%p**d==0
        r+=t*(delta//p**d*pow(slope,-1,p)%p)
        assert B(r,p,d+1,ord2)==target(p,w,d+1)
    return r,period_base*p**(k-1)

Q=35697042810
R=4152608179
for k in range(1,6):
    v3=full_lift(19,18,9,7,lambda r:12,3,k)
    v5=full_lift(67,66,165,49,lambda r:23,5,k)
    v6=full_lift(131,130,51090,12979,lambda r:390*pow(9,r,131),6,k)
    a,m=R,Q
    for b,n in [v3,v5,v6]:a,m=crt(a,m,b,n)
    if a==0:a=m
    assert a%3==1 and a%6==1
    assert B(a,4099,1,4098)==2059
    assert B(a,35,1,12)==20
    for p,ord2,w in [(19,18,3),(67,66,5),(131,130,6)]:
        assert B(a,p,k,ord2)==target(p,w,k)
    assert m==Q*(19*67*131)**(k-1)
    print(f'depth={k} index={a} period={m}')
print('PASS: one feeder with 3 homogeneous depth-k branches and five first parents')
