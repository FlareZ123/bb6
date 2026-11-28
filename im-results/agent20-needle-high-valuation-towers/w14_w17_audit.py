#!/usr/bin/env python3
"""Two independent p-adic cancellation feeder towers, valuation 14 and 17.

Exact original finite-geometric counter polynomial and modular exponentiation.
Finite regression; infinite derivation in README.md.
"""
R=4152608179
Q=35697042810
CASES=[
    (14,32771,32770,3277,R+Q*7824,Q*91756,14966,
     (24180,31030,11597,17015,17567,31431,1128,22070,2358)),
    (17,262147,262146,43691,R+Q*2976,Q*190885979,227076,
     (90594,223162,227468,255899,178617,28353,125014,219266,95082))
]

def geometric(x,y,n,m):
    if n==0:return 0
    if n==1:return 1
    h=geometric(x,y,n//2,m)
    even=h*(pow(x,n//2,m)+pow(y,n//2,m))%m
    return even if n%2==0 else (x*even+pow(y,n-1,m))%m

def feeder(r,p,ord2,k):
    m=p**k
    order=ord2*p**(k-1)
    a=((pow(9,r,2*order)+5)//2)%order
    A=pow(2,a,m)
    return pow(2,(a-1)%order,m)*(A-3)*geometric(A*A%m,9,r,m)%m

def target(w,p,k):
    return -2**w*(2*w-3)*pow(3,-1,p**k)%p**k

for w,p,E,N,base,S,sigma,coefficients in CASES:
    assert p==2**(w+1)+3 and S%E==0 and S%N==0
    q2=(pow(2,E,p*p)-1)//p
    q9=(pow(9,N,p*p)-1)//p
    alpha=2*(S//E)*q2%p
    beta=(S//N)*q9%p
    ar=((pow(9,base,p)+5)*pow(2,-1,p))%p
    A=pow(2,((pow(9,base,2*E)+5)//2)%E,p)
    ratio=A*pow(2*(A+3),-1,p)%p
    XA=pow(A,2*base,p);Y=pow(9,base,p)
    assert (q2,q9,alpha,beta,ar,A,ratio,XA,Y)==coefficients
    assert ratio*(alpha*ar*XA-beta*Y)%p==sigma
    assert feeder(base,p,E,1)==target(w,p,1)
    r=base
    print('valuation',w,'p',p,'base',base,'step',S,'unit slope',sigma)
    for k in range(1,8):
        step=S*p**(k-1);m=p**(k+1)
        assert feeder(r,p,E,k)==target(w,p,k)
        assert (feeder(r+step,p,E,k+1)-feeder(r,p,E,k+1))%m==sigma*p**k
        delta=(target(w,p,k+1)-feeder(r,p,E,k+1))%m
        assert delta%p**k==0
        r+=step*(delta//p**k*pow(sigma,-1,p)%p)
        assert feeder(r,p,E,k+1)==target(w,p,k+1)
        if k<=3:print('  k',k+1,'residue',r,'period',S*p**k)
print('PASS: valuation14 and 17, seven exact Hensel lifts each')
