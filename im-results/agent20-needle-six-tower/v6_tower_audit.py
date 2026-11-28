#!/usr/bin/env python3
"""Exact finite audit for 65 131-adic Space Needle v=6 inverse towers.

Reconstructs the original cancellation polynomial modulo 131^k, checks
the resonant CRT classification and seven lifts of every independent branch.
No floating point, third-party dependencies, or assumption of the lift formula.
"""
P=131
PERIOD=390*P

def geo(x,y,n,m):
    if n==0:return 0
    if n==1:return 1
    z=geo(x,y,n//2,m)
    v=z*(pow(x,n//2,m)+pow(y,n//2,m))%m
    return v if n%2==0 else (x*v+pow(y,n-1,m))%m

def feeder(r,k):
    m=P**k; order=130*P**(k-1)
    a=((pow(9,r,2*order)+5)//2)%order
    A=pow(2,a,m)
    return pow(2,(a-1)%order,m)*(A-3)*geo(A*A%m,9,r,m)%m

def target(k):
    m=P**k
    return (-576*pow(3,-1,m))%m

base=[]
for j in range(65):
    # CRT r=1 mod6, r=j mod65, r=70*(9^j)^(-1) mod131
    c=(1+6*((j-1)*pow(6,-1,65)%65))%390
    rp=70*pow(pow(9,j,P),-1,P)%P
    r=(c+390*((rp-c)*pow(390,-1,P)%P))%PERIOD
    if r==0:r=PERIOD
    assert r%6==1 and r%65==j and r%P==rp
    base.append(r)
assert len(set(base))==65
assert sorted(base)==[r for r in range(1,PERIOD+1) if r%6==1 and feeder(r,1)==70]
print('Exactly 65 CRT base index classes on resonant branch; first 12:', sorted(base)[:12])
for idx,r0 in enumerate(base):
    slope=390*pow(9,r0,P)%P
    assert slope!=0
    assert (feeder(r0+PERIOD,2)-feeder(r0,2))%(P*P)==slope*P
    r=r0
    for k in range(1,8):
        step=390*P**k
        m=P**(k+1)
        assert feeder(r,k)==target(k)
        assert (feeder(r+step,k+1)-feeder(r,k+1))%m==slope*P**k
        diff=(target(k+1)-feeder(r,k+1))%m
        assert diff%P**k==0
        digit=(diff//P**k)*pow(slope,-1,P)%P
        r+=digit*step
        assert feeder(r,k+1)==target(k+1)
    if idx<4:print('branch',idx,'base',r0,'slope',slope,'depth8 lifted',r)
print('PASS: 65 resonant branches, 7 Hensel lifts/branch, exact modular polynomial')
