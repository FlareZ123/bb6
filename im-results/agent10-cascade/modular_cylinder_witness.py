"""Exact examples for ModularCylinderDensity.md; no blank-root assertion."""
from math import gcd, lcm

def factors(n):
    p=2
    while p*p<=n:
        if n%p==0:
            e=0
            while n%p==0:
                n//=p
                e+=1
            yield p,e
        p+=1
    if n>1:
        yield n,1

def phi(n):
    x=n
    for p,_ in factors(n):
        x=x//p*(p-1)
    return x

def crt(x,m,y,n):
    g=gcd(m,n)
    assert (y-x)%g==0
    t=(y-x)//g*pow(m//g,-1,n//g)%(n//g) if n//g>1 else 0
    return (x+m*t)%lcm(m,n),lcm(m,n)

def selector(A,B,q,d0,L0):
    assert gcd(q,6)==1
    L=lcm(L0,q,phi(q))
    d,m=d0%L0,L0
    qf=dict(factors(q))
    for p,e in factors(L):
        pp=p**e
        if m%pp==0:
            continue
        if p in (2,3):
            d,m=crt(d,m,d%pp,pp)
            continue
        if p not in qf:
            d,m=crt(d,m,0,pp)
            continue
        for j in range(1,qf[p]+1):
            pj=p**j
            assert m%((p-1)*p**(j-1))==0
            val=(A*pow(2,d,pj)-B)*pow(2,-1,pj)%pj
            d,m=crt(d,m,val,pj)
        d,m=crt(d,m,d%pp,pp)
    assert m==L and (A*pow(2,d,q)-2*d-B)%q==0
    return d,m

def verify_chain(n,tokens,m,r,M,kappa):
    assert n>=257 and n%6 in (4,5)
    u=4*2**n-n-4
    for k,a in reversed(tokens):
        X=2*u+5
        assert X%3**a==0
        h=2**a*(X//3**a)-8*2**k-k-5
        assert h>=0
        assert 4*2**k<h+k+4 and h+k+5<8*2**k
        assert 2**(a+1)*X==3**a*(2*h+5+16*2**k+2*k+5)
        u=h
    assert h%m==r%m and k%M==kappa%M
    print(f'prepared chain: h mod {m}={r}, k mod {M}={kappa}, tokens={tokens}, fatal n={n}')

if __name__=='__main__':
    count=0
    for q in (5,7,11,25,35,55,77,275,385,1925):
        for B in range(q):
            selector(24,B,q,5,6)
            count+=1
    print(f'composite selector: {count} target residues passed')
    verify_chain(274,[(272,2)],1,0,1,0)
    verify_chain(274,[(272,0),(272,2)],2,0,2,0)
    verify_chain(292,[(288,1),(289,4)],4,1,4,0)
    verify_chain(9239,[(9234,7)],3,1,1,0)
    verify_chain(4865,[(4860,0),(4860,7)],6,4,2,0)
    verify_chain(6124,[(6120,1),(6121,4)],10,7,2,0)
    verify_chain(6124,[(6120,1),(6121,4)],20,17,4,0)
