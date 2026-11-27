#!/usr/bin/env python3
"""Exact finite audit of five valuation-five Space Needle cancellation towers."""
def geometric(a,b,n,m):
    if n == 0: return 0
    if n == 1: return 1
    h=geometric(a,b,n//2,m)
    v=h*(pow(a,n//2,m)+pow(b,n//2,m))%m
    return v if n%2 == 0 else (a*v+pow(b,n-1,m))%m
def feeder_mod(r,k):
    m=67**k; order=66*67**(k-1)
    a=((pow(9,r,2*order)+5)//2)%order
    A=pow(2,a,m)
    return pow(2,(a-1)%order,m)*(A-3)*geometric(A*A%m,9,r,m)%m
def target(k):
    m=67**k
    s=224*sum(pow(64,k-1-i,m)*pow(67,i,m) for i in range(k))%m
    return s*pow(pow(64,k,m),-1,m)%m
def direct(r):
    a=(9**r+5)//2; A=2**a; P=0
    for i in range(r): P=A*A*P+(A-3)*9**i
    return 2**(a-1)*P
assert target(1)==37
for r in range(1,5):
    for k in range(1,4): assert direct(r)%(67**k)==feeder_mod(r,k)
base=[r for r in range(1,166) if feeder_mod(r,1)==37]
assert base==[39,49,75,119,140],base
slopes=[18,23,33,65,49]
for r0,slope in zip(base,slopes):
    r=r0
    for k in range(1,9):
        m=67**(k+1);period=165*67**(k-1)
        assert feeder_mod(r,k)==target(k)
        assert (feeder_mod(r+period,k+1)-feeder_mod(r,k+1))%m==slope*67**k
        delta=(target(k+1)-feeder_mod(r,k+1))%m
        assert delta%(67**k)==0
        digit=delta//(67**k)*pow(slope,-1,67)%67
        r+=digit*period
        assert feeder_mod(r,k+1)==target(k+1)
        if k<=3: print('branch',r0,'depth',k+1,'index',r,'period',period*67)
print('PASS: five branches, eight depths, complete base census, direct polynomial audit')
