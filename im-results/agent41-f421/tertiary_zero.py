"""Conditional F421 tertiary-zero crossing and autonomous head recurrence."""
import hashlib
import random
import sys
from boundary import make, cells, single, drain
from cross_zero import seed
from verify_tertiary import marked, prefix_cycle, action
P,Q,Z,H='10','01','00','11'

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

def head_drain(us):
    h=2;out=[]
    for u in us:
        if u>h:out.append(u-h)
        h+=min(u,h)
    return out,h

def head_step(us,birth=True):
    a,A=head_drain(us);b,B=head_drain(a)
    v=[u+(1<<i) for i,u in enumerate(b)]
    if birth:v.append((1<<len(b))+A+B)
    return v

def head_of(b,cs):
    return [(q+1)//8 for p,q in reversed(cs[:-3])]+[(b+1)//8]

def zero_cross(w):
    a,b,cs,x,y,sc,U=unpack(w);m=len(cs);M=1<<m
    assert m>=3 and a==2*M-1 and b>=7 and (b+1)%8==0
    assert all(p>=3 for p,q in cs)
    assert all(q>=7 and (q+1)%8==0 for p,q in cs[:-3])
    assert all(q>=2*B+2 for (p,q),B in zip(cs[-3:],(4,2,1)))
    assert x>=3 and y>=2 and all(z>=2 and r>=2 and f==0 for z,r,f in sc)
    assert len(U)>=6 and [p for p,n in U[:6]]==[Q,Z,P,Z,P,H]
    z0,r0,v=U[0][1],U[2][1],U[4][1]
    assert U[1]==U[3]==(Z,1) and U[5]==(H,1) and min(z0,r0,v)>=2
    out=[];prev=b
    for p,q in cs:out.append((prev,p-1));prev=q
    out.append((prev,x-1))
    a1,b1,cs1,H1=marked(1,a+1,out)
    assert cs1[-1][1]==x and all(p>=3 for p,q in cs1)
    out=[];prev=b1
    for p,q in cs1:out.append((prev,p-1));prev=q
    aa,bb,cc,H2=marked(1,a1+1,out)
    N=1<<len(cs1)
    assert len(cc)==len(cs1) and H2==N-1 and aa==2*N-1 and bb==N+1+2*H1
    assert bb>=3*N-1
    t=[(P,x),(Z,1),(P,y)]
    for z,r,f in sc:t.extend([(Z,1),(Q,z),(P,r+1)])
    t.extend([(Z,1),(Q,z0),(P,r0),(Q,1),(P,v),(H,1)])
    return make(aa,bb,[(p,q,False) for p,q in cc],t+U[6:]),H1+H2+2

def exact_zero(w):
    w,c,o,t=single(w);assert o==1 and t=='011'
    w,k1,c=drain(w)
    w,c,o,t=single(w);assert o==1 and t=='00'
    w,k2,c=drain(w)
    return w,k1+k2+2

def test(n=300):
    rng=random.Random(4100)
    for _ in range(n):
        m=rng.randrange(3,10);a=2*(1<<m)-1;b=8*rng.randrange(1,500)-1
        cs=[(rng.randrange(3,500),8*rng.randrange(1,500)-1) for _ in range(m-3)]
        cs += [(rng.randrange(3,500),2*B+2+rng.randrange(1000)) for B in (4,2,1)]
        sc=[(rng.randrange(2,20),rng.randrange(2,20),0) for _ in range(rng.randrange(1,10))]
        U=[(Q,3),(Z,1),(P,5),(Z,1),(P,7),(H,1),(Z,1),(Q,1)]
        w=pack(a,b,cs,10,20,sc,U)
        assert zero_cross(w)==exact_zero(w)
        cs=[(p,q+100 if i>=m-3 else q) for i,(p,q) in enumerate(cs)]
        aa,bb,cc,K=prefix_cycle(a,b,cs)
        us=head_of(b,cs);vs=head_of(bb,cc)
        assert head_step(us)==vs
        assert sum(vs)==sum(us)+3+2**len(vs)
    print(n,'exact zero crossings and normalized-head comparisons passed')

def authentic_tail():
    sys.set_int_max_str_digits(0)
    w,K,odd=seed()
    while odd<65700:
        w,k,o=action(w);K+=k;odd+=o
    w,k,c=drain(w)
    digest=hashlib.sha256(('\n'.join(f'{p} {n}' for p,n in w)+'\n').encode()).hexdigest()
    assert digest=='a74ba0026d9a3d59b37216703669dd8d7c59f552c63cd5fa3c7efd38de75fab2'
    a,b,cs,x,y,sc,U=unpack(w);S=sum(f<<i for i,(_,_,f) in enumerate(sc));T=2*S+1
    assert len(sc)==8214 and S==2**8214-1
    end=[(z-(S>>i),r+((S>>i)+1)//2,0) for i,(z,r,f) in enumerate(sc)]
    assert min(U[0][1],U[2][1],U[4][1])>=2 and [p for p,n in U[:6]]==[Q,Z,P,Z,P,H]
    assert U[1]==U[3]==(Z,1) and U[5]==(H,1)
    assert all(z>=2 and r>=2 for z,r,f in end)
    assert x+S>=T+4 and y-S>=T+3
    r2=[r+1 for z,r,f in end]+[U[2][1]]
    assert all(r>=((T>>i)//2)+2 for i,r in enumerate(r2))
    assert all(q-3*B*S>=2*B+2 for (p,q),B in zip(cs,(4,2,1)))
    print('seed hash',digest,'next counter bits',T.bit_length(),'extra cell',U[:6])
    print('x//T,y//T',(x+S)//T,(y-S)//T,'all secondary tail budgets pass')
    cc=[(p,q-3*B*S) for (p,q),B in zip(cs,(4,2,1))]
    ww=pack(a,b,cc,x+S,y-S,end,U)
    assert zero_cross(ww)==exact_zero(ww)
    print('actual zero tail with synthetic primary: exact crossing matched')

if __name__=='__main__':
    if '--authentic' in sys.argv:authentic_tail()
    else:test()
