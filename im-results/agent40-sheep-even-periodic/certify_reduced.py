"""Stronger all-index Sheep even-return exclusions with complete cyclic checks.

Runs on Python >=3.10, standard library only. No dependence on sympy,
number theoretic oracles, long forward simulations or finite exponent horizons.
Mathematical proof of completeness: REDUCED_PERIODS.md.
"""
from dataclasses import dataclass
from functools import lru_cache
from math import gcd, lcm


@dataclass(frozen=True)
class Node:
    s: int
    b: int
    d: int


ROOT = Node(0,0,1)
CASES = (
    (648, 122472, {
        ROOT:{(5,2):Node(8,-1228,2187)},
        Node(8,-1228,2187):{},
    }),
    (864, 8777160, {
        ROOT:{(3,6):Node(10,-16576,3483)},
        Node(10,-16576,3483):{},
    }),
    (1002, 102060, {
        ROOT:{(1,1):Node(3,-2,15), (2,2):Node(5,-68,81)},
        Node(3,-2,15):{},
        Node(5,-68,81):{},
    }),
)


@lru_cache(None)
def factor(n):
    assert n >= 1
    out={}
    p=2
    while p*p <= n:
        while n%p == 0:
            out[p]=out.get(p,0)+1
            n//=p
        p=3 if p==2 else p+2
    if n>1: out[n]=out.get(n,0)+1
    return out


@lru_cache(None)
def order2(n):
    """Return a proven modular period; verified, not trusted as least order."""
    assert n>0 and n%2==1
    if n==1: return 1
    tot=n
    for p in factor(n):tot=tot//p*(p-1)
    candidate=tot
    for p in factor(tot):
        while candidate%p==0 and pow(2,candidate//p,n)==1:
            candidate//=p
    assert pow(2,candidate,n)==1, (n,candidate)
    return candidate


def high_h_cutoff(node,r,M):
    for H in range(1,18):
        m=node.d*3**H
        if ((pow(2,r+node.s,m)+node.b-node.d)%m != 0
            and pow(2,M,m)==1):
            return H
    raise AssertionError(('no valid universal 3-adic cutoff',node,r,M))


def high_a_cutoff(D,C):
    for A in range(1,60):
        q=D*(2*A-1)-2*C
        if q%2==1 and 1<q<2**A and 2*D<2**A:
            return A
    raise AssertionError(('no valid universal 2-adic cutoff',D,C))


def exceptional_bound(D,C,n):
    c=3*D
    e=c.bit_length()
    assert (1<<(e-1)) < c < (1<<e)
    assert n >= e+2
    assert ((1<<e)-c)*(1<<(n-e))>D*(n+3)+abs(C)
    assert (1<<(n-e))>2*D
    assert D*(n-e+4)>=C


def verify_node(node,r,M):
    s,b,d=node.s,node.b,node.d
    assert d>=1 and d%2==1 and s>=0
    assert d==1 or pow(2,M,d)==1
    assert (pow(2,r+s,d)+b)%d==0
    assert (1<<(r+s))+b>10*d
    H=high_h_cutoff(node,r,M)
    found={}
    log=[]
    for h in range(H):
        D=d*3**h
        C=(1<<h)*(b-d)+D
        A=high_a_cutoff(D,C)
        exceptional_bound(D,C,r+s+h)
        survivors=[]
        for a in range(1,A):
            T=D*((1<<(a+1))+1)
            B=2*C-D*(2*a-1)
            p=lcm(order2(D),order2(T))
            assert (D==1 or pow(2,p,D)==1) and pow(2,p,T)==1
            q=p//gcd(p,M)
            assert (D==1 or pow(2,M*q,D)==1) and pow(2,M*q,T)==1
            live=[]
            for k in range(q):
                j=r+M*k
                if ((pow(2,j+s,D)+b-d)%D==0
                   and (pow(2,j+s+h+1,2*T)+B)%(2*T)==T):
                    live.append(k)
            if live:
                child=Node(s+h+1+a,(1<<a)*B,T)
                found[(h,a)]=child
                survivors.append((a,q,tuple(live)))
        log.append((h,A,survivors))
    return H,found,log


def even_parents(y):
    """Independent exact integer E-predecessor cross-check at base exponent."""
    parents=set()
    h=0
    while (y-1)%(3**h)==0:
        z=1+(1<<h)*((y-1)//(3**h))
        for a in range(1,z.bit_length()):
            den=(1<<(a+1))+1
            val,rem=divmod(2*z-2*a+1,den)
            if rem==0 and val>=5 and val%2==1:
                parents.add((1<<a)*val)
            if 3*(1<<a)+a+3==z:
                parents.add(3*(1<<a))
        h+=1
    return sorted(parents)


def main():
    for r,M,tree in CASES:
        assert ROOT in tree
        assert set(tree)=={ROOT}|{child for child in tree[ROOT].values()}
        print('Family: j =',r,'+',M,'*k, k >= 0')
        for node,expected in tree.items():
            H,actual,log=verify_node(node,r,M)
            assert actual==expected,(r,node,actual,expected)
            val=((1<<(r+node.s))+node.b)//node.d
            direct=even_parents(val)
            predicted=sorted(((1<<(r+c.s))+c.b)//c.d for c in expected.values())
            assert direct==predicted,(r,node,direct,predicted)
            print('  node',node,'H=',H,'low-valuation table:',log)
        assert all(not child for n,child in tree.items() if n!=ROOT)
        print('PASS all natural k, exact exhaustive two-level inverse tree')


if __name__=='__main__':
    main()
