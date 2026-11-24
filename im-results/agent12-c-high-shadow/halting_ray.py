"""Construct a Machine C prepared halting ray in any residue class and slope interval.

Exact integer implementation of the paper proof. No blank reachability claim.
Coordinates are (A,M)=(a,a+2*k). build_ray returns (a,k), direction and
finite successful branch word followed by a terminal bounce. Every integer
parameter t>=0 on the returned ray satisfies the same certificate.
"""
from collections import deque
from fractions import Fraction
from dataclasses import dataclass


def prefix_word(lo: Fraction, hi: Fraction) -> list[int]:
    assert 0 <= lo < hi <= 1
    R = 1
    while True:
        P = 1 << R
        Q = int(lo * P) + 1
        Q += 1 - Q % 2
        if Fraction(Q + 1, P) < hi:
            bits = [i for i in range(R) if Q >> i & 1]
            return list(reversed([b-a for a,b in zip(bits,bits[1:]+[R])]))
        R += 1


def projected_step(s: tuple[int,int], r: int, d: int, L: int) -> tuple[int,int]:
    A,M = s
    o = M % 2
    w = 3*r+1
    b = 0 if r == 1 else (1<<r)*(2+o)-w-2*o
    return (((1<<r)*A-M+b)%d, (M+w)%L)


def steering_word(s: tuple[int,int], L: int, m: int) -> list[int]:
    h = L & -L
    d = L // h
    T = 1 << (2*m+2)
    D = 6*m+7
    assert T % h == 0
    def goal(s):
        A,M=s
        return (M+D)%h == 0 and (M-T*(A+3)+D)%d == 0
    parents={s:None}
    queue=deque([s])
    while queue:
        v=queue.popleft()
        if goal(v):
            word=[]
            while parents[v] is not None:
                v,r=parents[v]
                word.append(r)
            return word[::-1]
        for r in (1,2,3):
            w=projected_step(v,r,d,L)
            if w not in parents:
                parents[w]=(v,r)
                queue.append(w)
    raise AssertionError('modular steering theorem violated')


@dataclass(frozen=True)
class Linear:
    b: int
    d: int = 0
    def __add__(self, other):
        if isinstance(other,int): other=Linear(other)
        return Linear(self.b+other.b,self.d+other.d)
    __radd__=__add__
    def __neg__(self): return Linear(-self.b,-self.d)
    def __sub__(self, other): return self+-other
    def __rsub__(self, other): return -self+other
    def __mul__(self, k: int): return Linear(self.b*k,self.d*k)
    __rmul__=__mul__
    def at(self,t: int): return self.b+self.d*t


def build_ray(a0: int,k0: int,N: int,lo: Fraction,hi: Fraction):
    assert N>=1 and 0<=lo<hi<=1
    L=2*N
    h=L&-L
    d=L//h
    m=max(0,(h.bit_length()-2)//2)
    T=1<<(2*m+2)
    D=6*m+7
    A0=a0%L
    M0=(a0+2*k0)%L
    word=prefix_word(lo,hi)
    s=(A0%d,M0)
    for r in word: s=projected_step(s,r,d,L)
    word += steering_word(s,L,m)
    P,Q,C,W=1,0,0,0
    for r in word:
        o=(M0+W)%2
        w=3*r+1
        b=0 if r==1 else (1<<r)*(2+o)-w-2*o
        P,Q,C,W=(1<<r)*P,(1<<r)*Q+1,(1<<r)*C-W+b,W+w
    J=1+T*Q
    H=T*P
    rhs=W+D-T*(C+3)
    assert (rhs-H*A0+J*M0)%L==0
    S=(rhs-H*A0+J*M0)//L
    y=(-S*pow(J,-1,H))%H
    x=(S+J*y)//H
    A=Linear(A0+L*x,L*J)
    M=Linear(M0+L*y,L*H)
    originA,originM=A,M
    assert lo<Fraction(A.d,M.d)<hi
    threshold=0
    def ge(z: Linear,lower: int=0):
        nonlocal threshold
        if z.d>0:
            threshold=max(threshold,(lower-z.b+z.d-1)//z.d)
        else:
            assert z.d==0 and z.b>=lower, (z,lower)
    # Guarantee every point has a slope in the requested open interval.
    ge(lo.denominator*A-lo.numerator*M,1)
    ge(hi.numerator*M-hi.denominator*A,1)
    # Affine guards are verified coefficientwise for all t>=threshold.
    for r in word:
        ge(A,2); ge(M-A,2)
        o=M.b%2
        assert A.b%2==o and A.d%2==M.d%2==0
        if r==1:
            ge(2*A-M)
            A,M=2*A-M,M+4
        else:
            ge(M-2*A,1)
            K=A-1
            c=M-2*A+3
            for _ in range(r-2):
                if o==0:
                    ge(c-2*K-6,1)
                    K,c=2*K+3,c-2*K-3
                else:
                    ge(c-2*K-8,1)
                    K,c=2*K+4,c-2*K-5
            if o==0:
                ge(c,4); ge(2*K+6-c)
                X,Y=2*K+6-c,c
            else:
                ge(c,6); ge(2*K+8-c)
                X,Y=2*K+8-c,c-1
            W0=3*r+1
            assert X==((1<<r)*(A+2+o)-M-W0-2*o)
            assert X+2*Y==M+W0
            A,M=X,X+2*Y
    # Final terminal high-family bounce. The last recursive guard has
    # zero slope but constant 2, so it is included explicitly.
    ge(A,3);ge(M-A,2);ge(M-2*A,1)
    assert A.b%2==M.b%2==1
    assert M==T*(A+3)-D
    K,c=A-1,M-2*A+3
    for _ in range(2*m+1):
        ge(c-2*K-8,1)
        K,c=2*K+4,c-2*K-5
    assert c==Linear(5)
    a=originA.at(threshold)
    mass=originM.at(threshold)
    k=(mass-a)//2
    assert a%N==a0%N and k%N==k0%N
    return (a,k),(originA.d,(originM.d-originA.d)//2),word,m


def section(a: int,k: int):
    """Independent exact source case interpreter (returns output and branch r)."""
    if a<2 or k<1: raise AssertionError('unexpected special input')
    if a>=2*k: return (a-2*k,2*k+2),1
    K,c=a-1,2*k-a+3
    n=0
    while True:
        if c<4: return None,n+2
        if K%2:
            if c<=2*K+6:return (2*K+6-c,c),n+2
            K,c=2*K+3,c-2*K-3
        else:
            if c==4:return (2*K+2,3),n+2
            if c==5:return None,n+2
            if c<=2*K+8:return (2*K+8-c,c-1),n+2
            K,c=2*K+4,c-2*K-5
        n+=1


def check_ray(base,direction,word,m,t):
    p=tuple(b+d*t for b,d in zip(base,direction))
    for r in word:
        p,r_actual=section(*p)
        assert p is not None and r==r_actual
    end,r_actual=section(*p)
    assert end is None and r_actual==2*m+3


if __name__=='__main__':
    cases=[(1,0,0),(2,1,0),(3,2,1),(5,4,3),(12,5,8),(16,11,13),(60,17,23),(105,52,73)]
    ranges=[(Fraction(1,100),Fraction(1,80)),(Fraction(1,3),Fraction(2,5)),(Fraction(93,100),Fraction(97,100))]
    for N,a,k in cases:
        for lo,hi in ranges:
            base,direction,word,m=build_ray(a,k,N,lo,hi)
            for t in (0,1,31):check_ray(base,direction,word,m,t)
            print(f'N={N:3}, residue=({a},{k}), slope=({lo},{hi}), word={len(word):3}, m={m}, base bits={max(map(int.bit_length,base))}')
    print('All 24 constructed infinite halting rays checked coefficientwise; 72 sample replays passed.')
