"""All-n symbolic verification of near-power inverse trees on p=6*3^(R+2n)+c.
Q=9^n. Expr is A*Q+B*n+C. No sampling is used by verify().
The search suggests trees; the exact symbolic checks justify the families.
"""
from dataclasses import dataclass
from near_power import stats, SECTORS, initial
from fitfamilies import cert, match

@dataclass(frozen=True)
class Expr:
    a:int=0; b:int=0; c:int=0
    def __add__(self,o):
        if isinstance(o,int):o=Expr(c=o)
        return Expr(self.a+o.a,self.b+o.b,self.c+o.c)
    __radd__=__add__
    def __neg__(self):return Expr(-self.a,-self.b,-self.c)
    def __sub__(self,o):return self+-o
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):return Expr(self.a*o,self.b*o,self.c*o)
    __rmul__=__mul__
    def ge(self,n=0):
        """Sufficient all-n lower bound using 9^n>=1+n."""
        return self.a>=0 and self.a+self.b>=0 and self.a+self.c>=n
    def mod(self,m):
        assert m in (2,4,8) and self.b%m==0
        return (self.a+self.c)%m
    def eval(self,n):return self.a*9**n+self.b*n+self.c

N=Expr(b=1);Q=Expr(a=1)

def charge(w):
    r=2*w%3
    return (1,0) if r==0 else (-1,4) if r==1 else (-1,2)

def step(w):return (w+4*(2*w%3)-6)//3

STABLE={-3,-2,-1,0,1}

def dominance(k,W,B):
    """3^k >= (|W|+|B|+5)*9^n, so signed block positive (C>=1)."""
    M=(abs(W)+abs(B)+5).bit_length()
    assert (k-2*N).ge(M), (k,W,B)

def sym_stats(C,k,w):
    """Exact J,E as affine expressions in Q,n, checked for ALL n>=0."""
    assert C>0 and w.b==0 and (C+w.mod(2))%2==0
    W,B=w.a,w.c;J=Expr();E=Expr()
    while B not in STABLE:
        dominance(k,W,B)
        assert W%3==0,(W,B)
        j,e=charge(B);J+=j;E+=e
        W//=3;B=step(B);k-=1
    # The residual low component remains fixed or returns every two steps.
    dominance(k,W,B)
    # For all n, C*3^(k-2n)+W is large positive by dominance.
    if B in (-2,0):E+=2*N
    else:
        j,e=charge(B);J+=2*j*N;E+=2*e*N
    k-=2*N;B+=W
    while B not in STABLE:
        dominance(k,0,B)
        j,e=charge(B);J+=j;E+=e
        B=step(B);k-=1
    assert k.ge(2)
    if B in (-2,0) and k.mod(2)==1:
        assert k.ge(3)
        j,e=charge(B);J+=j;E+=e
        B=step(B);k-=1
    j,e=stats(C,2,B);J+=j;E+=e
    if B in (-2,0):E+=k-2
    else:
        j,e=charge(B);J+=j*(k-2);E+=e*(k-2)
    return J,E

def guard(C,D,k,u,v):
    """Prove x>=2*(floor(log2 y)+1), y>14 for all n."""
    assert C>0 and D>0 and u.b==v.b==0
    dominance(k-1,u.a,u.c);dominance(k-1,v.a,v.c)
    # x >= 3^(k-1), y <= (D+1)*3^k, y >= 3^(k-1).
    # For all k>=m, 3^(k-1)>=4*k+2*bit_length(D+1)+2.
    m=8+(D+1).bit_length()
    assert k.ge(m)
    assert 3**(m-1)>=4*m+2*(D+1).bit_length()+2

def expr_fit(pair,R,d):
    A,B=pair
    assert R>=d
    return Expr(a=A*3**(R-d),c=B)

def verify(t,R,off,d=0,expected=None,coeff=6):
    (C,D,u0,v0),edges=t
    u=expr_fit(u0,R,d);v=expr_fit(v0,R,d)
    k=Expr(a=coeff*3**R,c=off-d)
    guard(C,D,k,u,v)
    if d==0: expected=(1,13,k,Expr(c=-5),7-4*k)
    if expected is not None:assert (C,D,k,u,v)==expected
    ypar=((D*(1 if k.mod(2)==0 else 3)+v.mod(4))%4)//2
    assert (D*(1 if k.mod(2)==0 else 3)+v.mod(4))%2==0
    seen=set();nodes=1;mx=0
    for name,w0,kind,ch in edges:
        s=next(s for s in SECTORS if s[0]==name)
        _,z,par,left,ca,cd=s
        assert (ypar-z)%2==par and name not in seen;seen.add(name)
        w=expr_fit(w0,R,d+1)
        assert (D*(1 if (k-1).mod(2)==0 else 3)+w.mod(4))%4==2*par
        J,E=sym_stats(D,k-1,w);F=3*w+2*(E+z)
        if kind=='gap':
            _,E2=sym_stats(D,k-1,w+4);F2=3*(w+4)+2*(E2+z)
            assert (v-F).ge(1) and (F2-v).ge(1),(name,k,w,v,F,F2)
            assert ch is None
        else:
            assert F==v,(name,k,w,v,F)
            if left:child=(3*C+D,D,k-1,u-2*J+w+2*ca,w+2*cd)
            else:child=(D,3*C+D,k-1,w+2*ca,u-2*J+w+2*cd)
            cC,cD,ck,cu,cv=child
            ap=((cC*(1 if ck.mod(2)==0 else 3)+cu.mod(4))%4)//2
            dp=((cD*(1 if ck.mod(2)==0 else 3)+cv.mod(4))%4)//2
            if kind=='par':assert ap==1 or dp!=int(name in ('LO','RO'))
            else:
                assert kind=='hit' and ch is not None
                n,dep=verify(ch,R,off,d+1,child,coeff);nodes+=n;mx=max(mx,dep+1)
    assert len(seen)==2
    return nodes,mx

if __name__=='__main__':
    successes=[]
    for R in (30,31):
        for off in range(-100,102,2):
            cs=[cert(initial(6*3**r+off)) for r in (R,R+2,R+4)]
            if any(c is None for c in cs):continue
            t=match(cs,R)
            if not t:continue
            try:
                nodes,dep=verify(t,R,off)
            except AssertionError:
                # Failed sufficient symbolic guard: unknown, never exclusion.
                continue
            successes.append((R,off,nodes,dep));print('PROVED',R,off,nodes,dep)
    print('TOTAL',len(successes));print('deepest',max(successes,key=lambda s:s[3]))
