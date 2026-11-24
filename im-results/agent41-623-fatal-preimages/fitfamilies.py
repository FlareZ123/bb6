"""Discover candidate affine inverse trees; symbolic_exclusion checks them for all n."""
from near_power import State, initial, stats, SECTORS, pow3_ge

def cert(s, depth=100):
    if depth==0: return None
    n=s.budget();C,D,k,u,v=s.C,s.D,s.k,s.u,s.v
    if k<1 or not pow3_ge(k,max(4*n-u,30-v,1)):return None
    res=[]
    for name,z,par,left,ca,cd in SECTORS:
        if (s.yparity()-z)%2!=par:continue
        w_lo=(v-2*z-8*n+2)//3; w_hi=(v-2*z)//3
        w0=(2*par-D*pow(3,k-1,4))%4
        lo=(w_lo-w0+3)//4;hi=(w_hi-w0)//4
        hit=False
        while lo<=hi:
            m=(lo+hi)//2;w=4*m+w0;J,E=stats(D,k-1,w);f=3*w+2*(E+z)
            if f==v:hit=True;break
            if f<v:lo=m+1
            else:hi=m-1
        if not hit:
            w=4*(lo-1)+w0; J,E=stats(D,k-1,w)
            assert 3*w+2*(E+z)<v<3*(w+4)+2*(stats(D,k-1,w+4)[1]+z)
            res.append((name,w,'gap',None));continue
        Ap=(s.xparity()-J)%2
        if left:
            valid=(Ap+par+ca)%2==0;ch=State(3*C+D,D,k-1,u-2*J+w+2*ca,w+2*cd)
        else:
            valid=(par+ca)%2==0 and (Ap+par+cd)%2==(name=='RO');ch=State(D,3*C+D,k-1,w+2*ca,u-2*J+w+2*cd)
        if not valid:res.append((name,w,'par',None));continue
        c=cert(ch,depth-1)
        if c is None:return None
        res.append((name,w,'hit',c))
    return (s,res)

def depth(c):return 1+max([depth(ch) for _,_,_,ch in c[1] if ch]+[0])
def fit(a,b,c,r):
    if r<0:return None
    P=3**r
    d=b-a
    if d%(8*P):return None
    A=d//(8*P);B=a-A*P
    if A*81*P+B != c:return None
    return A,B

def match(cs,r,d=0):
    s1,s2,s3=[c[0] for c in cs]
    if len({(s.C,s.D,s.k-(6*3**(r+2*i))) for i,s in enumerate((s1,s2,s3))})!=1:return None
    u=fit(s1.u,s2.u,s3.u,r-d);v=fit(s1.v,s2.v,s3.v,r-d)
    if u is None or v is None:return None
    L=[]
    for tup in zip(*(c[1] for c in cs)):
        names,ws,types,children=zip(*tup)
        if len(set(names))!=1 or len(set(types))!=1:return None
        w=fit(*ws,r-d-1)
        if w is None:return None
        ch=match(children,r,d+1) if types[0]=='hit' else None
        if types[0]=='hit' and ch is None:return None
        L.append((names[0],w,types[0],ch))
    return ((s1.C,s1.D,u,v),L)
