#!/usr/bin/env python3
"""Exact modular regression for the 4099-adic valuation-eleven Needle tower.

Original cancellation polynomial evaluated independently, without a 4099-adic
derivative shortcut. Finite regression, not the all-depth paper proof.
"""
P=4099
Q=35697042810
R=4152608179
ORD2=4098

def geometric(x,y,n,m):
    if n==0:return 0
    if n==1:return 1
    z=geometric(x,y,n//2,m)
    v=z*(pow(x,n//2,m)+pow(y,n//2,m))%m
    return v if n%2==0 else (x*v+pow(y,n-1,m))%m

def feeder(r,k):
    m=P**k
    order=ORD2*P**(k-1)
    a=((pow(9,r,2*order)+5)//2)%order
    A=pow(2,a,m)
    return pow(2,(a-1)%order,m)*(A-3)*geometric(A*A%m,9,r,m)%m

def target(k):
    m=P**k
    return -38912*pow(3,-1,m)%m

q2=((pow(2,4098,P*P)-1)//P)%P
q9=((pow(9,683,P*P)-1)//P)%P
alpha=2*(Q//4098)*q2%P
beta=(Q//683)*q9%P
a=((pow(9,R,P)+5)*pow(2,-1,P))%P
A=48; zA=pow(A,2*R,P); z9=pow(9,R,P)
ratio=A*pow(2*(A+3),-1,P)%P
slope=ratio*(alpha*a*zA-beta*z9)%P
assert (q2,q9,alpha,beta,a,A,zA,z9,ratio,slope)==(
    239,45,3314,3930,1480,48,2719,2955,3135,2144)
assert feeder(R,1)==target(1)==2059
print('Source-level modular derivative coefficients verified, slope=',slope)
r=R
for k in range(1,9):
    step=Q*P**(k-1)
    m=P**(k+1)
    assert feeder(r,k)==target(k)
    assert (feeder(r+step,k+1)-feeder(r,k+1))%m==slope*P**k
    diff=(target(k+1)-feeder(r,k+1))%m
    assert diff%P**k==0
    digit=diff//P**k*pow(slope,-1,P)%P
    r+=digit*step
    assert feeder(r,k+1)==target(k+1)
    if k<=5:print('depth',k+1,'index',r,'period',Q*P**k,'new digit',digit)
print('PASS: eight exact 4099-adic lifts, unit derivative, pinned index R')
