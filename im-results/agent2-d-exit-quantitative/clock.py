"""Exact D first-event clock in original frozen-state-6 convention.
Scanned and right word are little-endian; canonical suffix includes delimiter.
Uses source-proved prefix, A-token, guard and B/D sweep identities.
"""
from functools import lru_cache
from fractions import Fraction as F
RULES=((1,1,1),(0,1,4),(1,-1,2),(0,1,0),(1,-1,0),(1,-1,3),(1,-1,2),(1,-1,5),(0,-1,2),(0,-1,1),(1,-1,4),None)
@lru_cache(None)
def service(q,w):
    tr=RULES[2*q+w%2]
    if tr is None:return -1,0,1
    b,d,r=tr
    if d<0:return r,2*(w//2)+b,1
    r,z,t=service(r,w//2)
    if r<0:return -1,0,t+1
    r,v,t2=service(r,2*z+b)
    return r,v,t+t2+1

def normalize(n,s,t):
    while s&1:s>>=1;n+=1
    return n,s,t

def e_guard(m,s,t):
    q=4
    guard=(0,0,1,0,1,0,1,0)
    for p in range(9):
        if p>=2 and p%2==0 and q in (1,3) and s%2==0:
            c=2*m+5-p
            return normalize(c,s>>1,t+c)
        if q==5 and s%2:return None,None,t+1
        assert p<8,(m,s,q,p)
        q,z,c=service(q,s);t+=c
        if q<0:return None,None,t
        s=2*z+guard[p]
    raise AssertionError('guard proof violated')

def event(n,s):
    assert n>=2 and s%2==0
    r=n%3;k=(n-(3,4,2)[r])//3;m=4*k+3
    t=12*k*k+41*k+(32,33,31)[r]
    if r==2:return normalize(2*m+3,s>>1,t+2*m+3)
    if r==1:return e_guard(m,s,t)
    v=s>>1
    while v&1:
        if v%4==1:v>>=2;t+=2;m+=1
        elif v%8==7:v>>=3;t+=6*m+41;m+=4
        else:return e_guard(m+1,v>>2,t+3)
    return normalize(2*m+5,v>>1,t+2*m+6)

def rank(w):return w.bit_length()+2*sum((w>>i)%8==6 for i in range(w.bit_length()))

def raw_event(n,s,cap=10**6):
    q=5;h=0;tape=set(range(1,n+1));tape|={n+1+i for i in range(s.bit_length()) if s>>i&1}
    for t in range(1,cap+1):
        tr=RULES[q*2+(h in tape)]
        if tr is None:return None,None,t
        b,d,q=tr
        if b:tape.add(h)
        else:tape.discard(h)
        h+=d
        if q==5 and h not in tape and not any(x<h for x in tape):
            w=sum(1<<(x-h-1) for x in tape)
            return normalize(0,w,t)
    raise RuntimeError((n,s,cap))

def test():
    for n in range(2,20):
        for s in range(0,64,2):
            a=event(n,s);b=raw_event(n,s)
            assert a==b,(n,s,a,b)
    print('576 literal raw first-event tests passed')

ANCHORS=((5,15,10),(9,36,10),(15,92,10),(39,403,9))
a=F(8,3)
def B(R):return 24*R**2+67*R+52+315*(2*R+88)*(R+51)
def clock_upper(n,R):return F(4,3)*n*n+(8*R+17)*n+B(R)

def anchor_data():
    out=[]
    for seed,C,h in ANCHORS:
        n,s=seed,0
        for j in range(h):
            n1,s1,t=event(n,s);assert n1 is not None
            assert F(4,3)*n*n<=t<=clock_upper(n,rank(s))
            assert rank(s1)<=rank(s)+11
            assert 3*n1>=8*n-23 and 3*(n1+rank(s1))<=8*(n+rank(s))+27
            n,s=n1,s1;C+=t
        L=5*n-23;U=5*(n+rank(s))+27
        out.append((seed,n,s,rank(s),C,L,U))
    return out

def bands(data):
    out=[]
    for seed,n,s,R,C,L,U in data:
        R1=R+11
        lo=min(C,F(12,55)*F(L,5)**2)
        hi=max(C,F(12,55)*F(U,5)**2)+(8*R1+17)*F(U,5)/(a-1)/a+655*(R1+51)**2/a**2
        out.append((seed,lo,hi))
    return out

def disjoint(b):return all(b[i][2]<b[i+1][1] for i in range(len(b)-1)) and b[-1][2]<a*a*b[0][1]

if __name__=='__main__':
    test();data=anchor_data();print('seed, anchor n, suffix, rank, exact clock, L, U:')
    for row in data:print(row)
    b=bands(data);assert disjoint(b)
    for seed,lo,hi in b:print(seed,lo,hi,'normalized interval',float(lo),float(hi))
    assert 2/a<1 and 2*F(73,62)**2/a**2<1
    assert 655>=24+630
    assert 2*655*51>=67+315*(102+88)
    assert 655*51**2>=52+315*88*51
    print('all comparisons exact; printed floats only illustrative')
