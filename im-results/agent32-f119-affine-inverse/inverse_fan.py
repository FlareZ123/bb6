from dataclasses import dataclass
from math import gcd
from collections import Counter
from fractions import Fraction

@dataclass(frozen=True,slots=True)
class Node:
    D:int=1
    B:int=0
    H:int=0
    e:int=0
    P:int=1
    # x=(3^(n+H)-B)/D, n≡e (mod P)
    def x(self,n):
        return (3**(n+self.H)-self.B)//self.D

def crt(a,m,b,n):
    g=gcd(m,n)
    if (b-a)%g:return None
    M=m//g;N=n//g
    k=((b-a)//g*pow(M,-1,N))%N if N>1 else 0
    return (a+m*k)%(m*N),m*N

def exp_lift(n:Node,C:int,M:int,t:int):
    # exact exponent order of 3 mod M=3^(t+1)+1 is 2(t+1)
    v=C%M
    s=None
    a=1
    for i in range(t+1):
        if a==v:s=i;break
        if M-a==v:s=i+t+1;break
        a*=3
    if s is None:return None
    ans=crt(n.e,n.P,(s-n.H)%(2*(t+1)),2*(t+1))
    if ans is None:return None
    e,P=ans
    m=n.D*M;g=gcd(n.D,M);L=m//g
    A=pow(3,e+n.H,m);J=pow(3,P,m)
    C%=m
    assert (C-A)%L==0 and (J-1)%L==0
    q=((J-1)//L*A)%g
    z=((C-A)//L)%g
    f=gcd(q,g)
    if z%f:return None
    d=g//f
    k=(z//f*pow(q//f,-1,d))%d if d>1 else 0
    e=(e+P*k)%(P*d);P*=d
    assert pow(3,e+n.H,m)==C and pow(3,P,m)==1%m
    return e,P

def children(n:Node):
    # Offset K2 grows linearly; once cutoff holds it persists.
    p=1;h=0
    while True:
        k2=n.B+n.D*(h+4)-(2*n.D-2)//3
        if h>=2 and 3*(k2-1)<2*p and k2>1:
            if 4*p>3*n.D:break
        M=3*p+1
        for r in (1,2):
            C=n.B+n.D*(r*p+h+r+2)
            ep=exp_lift(n,C,M,h)
            if ep is not None:
                e,P=ep
                D=n.D*M;B=3*p*n.B+n.D*p*(3*h+2*r+6);H=n.H+h+1
                child=Node(D,B,H,e,P)
                assert D%3==1 and pow(3,e+H,D)==B%D
                yield child,(h,r)
        p*=3;h+=1

def root_hit(n:Node,target=4):
    a=n.D*target+n.B
    q=0
    while a and a%3==0:a//=3;q+=1
    if a!=1:return None
    e=q-n.H
    return e if e>=1 and (e-n.e)%n.P==0 else None

if __name__=='__main__':
    import sys,time
    maxd=int(sys.argv[1]) if len(sys.argv)>1 else 8
    front=[(Node(),())];start=time.time()
    for d in range(maxd):
        new=[];dist=Counter();maxP=0;maxH=0;minp=10**100
        for n,path in front:
            hit=root_hit(n)
            if hit is not None:
                print('NECESSARY ROOT HIT (check guards)',hit,n,path);sys.exit()
            for ch,edge in children(n):
                new.append((ch,path+(edge,)));dist[edge[0]]+=1;maxP=max(maxP,ch.P.bit_length());maxH=max(maxH,ch.H);minp=min(minp,ch.P)
        dens=sum((Fraction(1,n.P) for n,path in new),Fraction(0)) if len(new)<500 else None
        print('depth',d+1,'front',len(new),'Hmax',maxH,'period bits',maxP,'minP',minp,'density',float(dens) if dens is not None else None,'edges',dict(dist),'sec',round(time.time()-start,2),flush=True)
        front=new
        if not front:print('CLOSED');break
        if len(front)>20000:print('STOP size');break
