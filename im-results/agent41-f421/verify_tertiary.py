"""F421 post-zero tertiary countdown: reproduce seed and test exact one-cycle map."""
import hashlib
import random
import sys
from boundary import make, cells, drain, carry, single, scan
from cross_zero import seed

P,Q,Z,H='10','01','00','11'

def marked(a,b,cs):
    """All-marked primary drain; exact endpoint from BoundaryEpoch.md."""
    h=merge=0;rev=[]
    for p,q in reversed(cs):
        cap=2*h+1
        if p<=cap:
            assert p%2==1, ('nonterminal',p,cap)
            t=(p+1)//2;merge+=q+t
        else:
            t=h+1;rev.append((p-cap,q+t+merge));merge=0
        h+=t
    return a+2*h,b+h+merge,rev[::-1],h

def prefix_cycle(a,b,cs):
    """Tertiary primary endpoint; the last Q is discarded into the tail."""
    out=[];prev=b
    for p,q in cs:
        assert p>=3
        out.append((prev,p-1));prev=q
    out.append((prev,3)) # dummy x-1; far cell survives both passes
    a1,b1,cs1,k1=marked(1,a+1,out)
    assert all(p>=2 for p,q in cs1)
    a2,b2,cs2,k2=marked(a1+2,b1+1,[(p-1,q) for p,q in cs1])
    out=[];prev=b2
    for p,q in cs2:
        assert p>=3
        out.append((prev,p-1));prev=q
    a3,b3,cs3,k3=marked(1,a2+1,out)
    assert len(cs3)==len(cs2)
    return a3,b3,cs3,k1+k2+k3+3

def unpack(w):
    a,b,cs,t=cells(w)
    assert all(not e for p,q,e in cs)
    assert t[0][0]==P and t[1]==(Q,1) and t[2][0]==P and t[3]==(H,1)
    sec=[];i=4
    while i+3<len(t) and t[i][0]==Q and t[i+1][0]==Z and t[i+1][1] in (1,2) and t[i+2][0]==P and t[i+3]==(H,1):
        sec.append((t[i][1],t[i+2][1],t[i+1][1]-1));i+=4
    return a,b,[(p,q) for p,q,e in cs],t[0][1],t[2][1],sec,t[i:]

def pack(a,b,cs,x,y,sec,U):
    t=[(P,x),(Q,1),(P,y),(H,1)]
    for z,r,f in sec:t.extend([(Q,z),(Z,1+f),(P,r),(H,1)])
    return make(a,b,[(p,q,False) for p,q in cs],t+U)

def guard(a,b,cs,x,y,sec,U):
    S=sum(f<<i for i,(_,_,f) in enumerate(sec))
    assert len(cs)>=3 and a==2*(1<<len(cs))-1 and b>=7 and (b+1)%8==0
    assert all(p>=3 for p,q in cs)
    assert all(q>=7 and (q+1)%8==0 for p,q in cs[:-3])
    assert all(q>=3*B*S+B+2 for (p,q),B in zip(cs[-3:],(4,2,1)))
    assert x>=3 and y>=S+2 and all(z>=(S>>i)+2 and r>=2 for i,(z,r,f) in enumerate(sec))
    return S

def predicted_cycle(w):
    a,b,cs,x,y,sec,U=unpack(w);S=guard(a,b,cs,x,y,sec,U);assert S
    j=(S&-S).bit_length()-1
    ns=[(z-1,r,1) if i<j else (z-1,r+1,0) if i==j else (z,r,f) for i,(z,r,f) in enumerate(sec)]
    aa,bb,cc,K=prefix_cycle(a,b,cs)
    nw=pack(aa,bb,cc,x+1,y-1,ns,U)
    assert guard(*unpack(nw))==S-1
    return nw,K

def action(w):
    _,_,cs,_=cells(w);V=sum(e<<j for j,(_,_,e) in enumerate(cs))
    if V:
        d=drain(w)
        if d is not None:return d[0],d[1],0
        v,k,_=carry(w,V)
        if k:return v,k,0
    v,_,odd,_=single(w)
    return v,1,odd

def exact_cycle(w):
    K=odd=0
    for _ in range(10000):
        if odd==2:
            _,_,cs,_=cells(w)
            if not any(e for _,_,e in cs):return w,K
        w,k,o=action(w);K+=k;odd+=o
        assert odd<=2
    raise AssertionError('diagnostic action cap')

def test(n=300):
    rng=random.Random(41)
    for _ in range(n):
        fs=[rng.randrange(2) for i in range(rng.randrange(1,6))];fs[rng.randrange(len(fs))]=1
        S=sum(f<<i for i,f in enumerate(fs));m=rng.randrange(3,8);a=2*(1<<m)-1;b=8*rng.randrange(1,100)-1
        cs=[(rng.randrange(3,200),8*rng.randrange(1,100)-1) for _ in range(m-3)]
        cs += [(rng.randrange(3,100),3*B*S+B+2+rng.randrange(100)) for B in (4,2,1)]
        sec=[((S>>i)+2+rng.randrange(20),rng.randrange(2,20),f) for i,f in enumerate(fs)]
        w=pack(a,b,cs,10,S+5,sec,[(Z,1),(Q,1)])
        assert predicted_cycle(w)==exact_cycle(w)
    print(n,'randomized exact tertiary cycles matched')

def authentic():
    with open('prefix-state.txt','rb') as f:
        assert hashlib.sha256(f.read()).hexdigest()=='f5e445d70cf1b2fc1982201911c6557b6c2b9fd5a1b9ee082e21be31758f2f87'
    w,K,odd=seed()
    while odd<65700:
        w,k,o=action(w);K+=k;odd+=o
    w,k,_=drain(w);K+=k
    a,b,cs,x,y,sec,U=unpack(w);S=guard(a,b,cs,x,y,sec,U)
    assert len(cs)==3 and len(sec)==8214 and S==2**8214-1
    sys.set_int_max_str_digits(0)
    digest=hashlib.sha256(('\n'.join(f'{p} {n}' for p,n in w)+'\n').encode()).hexdigest()
    assert digest=='a74ba0026d9a3d59b37216703669dd8d7c59f552c63cd5fa3c7efd38de75fab2'
    print('authentic odd',odd,'primary',len(cs),'tertiary bits',S.bit_length(),'seed sha256',digest)
    assert predicted_cycle(w)==exact_cycle(w)
    print('authentic cycle matched; all tail and fixed-suffix budgets hold for S cycles')

if __name__=='__main__':
    if '--authentic' in sys.argv:authentic()
    else:test()
