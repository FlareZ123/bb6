"""Exact inverse near-power coordinates without exponential integer construction."""
from dataclasses import dataclass
from functools import lru_cache
from collections import Counter
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "agent49-parity623"))

def pow3_ge(k, n):
    """3**k >= n without constructing huge 3**k."""
    if n <= 1 or k >= n.bit_length():
        return True
    return 3**k >= n

@lru_cache(maxsize=500000)
def stats(C,k,w):
    """Positive-budget drift, excess for b=(C*3**k+w)/2.
    C>0, k>=0; numerator even, b>=0. Collapse the eventual residual cycle.
    """
    assert C>0 and k>=0 and (C+w)%2==0
    J=E=0
    # Ensure b positive before each symbolic transition. For small b fallback.
    while k and pow3_ge(k, max(1,2-w)):
        if w in (-3,-1,1) and k>2:
            m=k-2
            J += m*(1 if w==-3 else -1)
            E += m*{-3:0,-1:4,1:2}[w]
            k=2
            continue
        if w in (-2,0) and k>3:
            m=(k-2)//2
            # residues 2,0; opposite first drifts, excess 2 per pair
            E+=2*m
            k-=2*m
            continue
        r=(2*w)%3
        J+=1 if r==0 else -1
        E+=(0,4,2)[r]
        w=(w+4*r-6)//3
        k-=1
    b=(C*3**k+w)//2
    assert b>=0
    while b:
        q,r=divmod(b,3)
        J+=1 if r==0 else -1
        E+=(0,4,2)[r]
        b=q+r-1
    return J,E

@dataclass(frozen=True)
class State:
    C:int
    D:int
    k:int
    u:int
    v:int
    def __post_init__(self):
        assert self.C>0 and self.D>0 and self.k>=0
        assert (self.C+self.u)%2==(self.D+self.v)%2==0
    def actual(self):
        P=3**self.k
        return ((self.C*P+self.u)//2,(self.D*P+self.v)//2)
    def budget(self):
        return 2*self.k+max(self.D.bit_length(),abs(self.v).bit_length())+2
    def xparity(self):
        return (self.C*pow(3,self.k,4)+self.u)%4//2
    def yparity(self):
        return (self.D*pow(3,self.k,4)+self.v)%4//2

# name, z, block parity, left, a_offset, d_offset
SECTORS=(('LO',5,0,True,2,-3),('LE',2,0,True,0,-2),('RO',3,1,False,1,-3),('RE',0,1,False,-1,-2))

def parents(s):
    """Complete even-first preimages, or None if a sufficient guard fails.
    No exponential integer construction. None means unknown, not empty.
    """
    C,D,k,u,v=s.C,s.D,s.k,s.u,s.v
    n=s.budget()
    if k<1 or not pow3_ge(k,max(4*n-u,30-v,1)):
        return None
    result=[]
    for name,z,par,left,ca,cd in SECTORS:
        if (s.yparity()-z)%2!=par:
            continue
        w_lo=(v-2*z-8*n+2)//3
        w_hi=(v-2*z)//3
        # Require b>=4 throughout the interval, to validate reconstruction.
        if not pow3_ge(k-1,max(1,8-w_lo)):
            return None
        w0=(2*par-D*pow(3,k-1,4))%4
        lo=(w_lo-w0+3)//4;hi=(w_hi-w0)//4
        while lo<=hi:
            m=(lo+hi)//2;w=4*m+w0
            J,E=stats(D,k-1,w)
            f=3*w+2*(E+z)
            if f==v:
                # Positive budget and large blocks imply the correct branch.
                Ap=(s.xparity()-J)%2
                if left:
                    if (Ap+par+ca)%2==0:
                        result.append((name,State(3*C+D,D,k-1,u-2*J+w+2*ca,w+2*cd)))
                else:
                    if (par+ca)%2==0 and (Ap+par+cd)%2==(name=='RO'):
                        result.append((name,State(D,3*C+D,k-1,w+2*ca,u-2*J+w+2*cd)))
                break
            if f<v:lo=m+1
            else:hi=m-1
    return result

def initial(p):return State(1,13,p,-5,7-4*p)

def maxdepth(s,limit=100):
    todo=[(s,0)];mx=0;nodes=0
    while todo:
        q,d=todo.pop();nodes+=1;mx=max(d,mx)
        if d>=limit:return mx,nodes,False
        ps=parents(q)
        if ps is None:return mx,nodes,False
        todo.extend((p,d+1) for _,p in ps)
    return mx,nodes,True

if __name__=='__main__':
    from inverse623 import full_stats, predecessors
    from random import Random
    rng=Random(41)
    for _ in range(10000):
        C=rng.randrange(1,10000);k=rng.randrange(0,200);w=rng.randrange(-1000,1000);w+=(C+w)%2
        b=(C*3**k+w)//2
        if b<0:continue
        assert stats(C,k,w)==full_stats(b)[:2],(C,k,w)
    for _ in range(1000):
        C=rng.randrange(1,100);D=rng.randrange(1,100);k=rng.randrange(10,100);u=rng.randrange(-100,100);v=rng.randrange(-100,100);u+=(C+u)%2;v+=(D+v)%2
        s=State(C,D,k,u,v)
        pp=parents(s)
        if pp is not None:
            a={p.actual() for _,p in pp};b=set(predecessors(s.actual(),even_only=True));assert a==b,(s,a,b)
    print('all random regressions passed')
    counts=Counter();longest=(0,0,0)
    for p in range(8,20000,2):
        d,n,c=maxdepth(initial(p));counts[d,c]+=1
        if d>longest[0]:longest=(d,p,n);print('record',longest,flush=True)
    print(counts)
    for p in (10**6,10**9,10**18,10**100):
        print(p,maxdepth(initial(p)))
