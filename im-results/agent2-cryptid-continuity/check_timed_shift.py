"""Independent exact-integer regression for DRegular 3-adic time curvature.

Stand-alone Python 3.11+. Seed 20261104. Source arithmetic independently
transcribed from byte-pinned original eleven-case DRegular.lean; does not use
a generated Lean file, package, or simulator to compute expected values.
"""
from dataclasses import dataclass
import random


@dataclass(frozen=True)
class L:
    a: int
    q: int
    b: int


def nxt(s: L) -> L | None:
    a, q, b = s.a, s.q, s.b
    if a % 3 == 2:
        k = a // 3
        return (L(8*k+9,0,0) if q == 0 else
                L(8*k+10+b,0,0) if q == 1 else L(8*k+10,q-1,b))
    if a % 3 == 0:
        k = a//3-1; r = (b+1)//3; d = q-1+4*r
        return (L(8*k+11,0,0) if q == 0 else
                L(8*k+11+2*d,0,0) if (b+1)%3 == 0 else
                L(8*k+13+2*d,0,0) if (b+1)%3 == 1 else
                L(8*k+7+2*d,1,5))
    k = a//3-1
    if q == 0: return L(8*k+5,1,5)
    if b == 0: return L(8*k+5,1,2*q+5)
    if b == 1: return None
    if b == 2: return L(8*k+9,q+1,0)
    return L(8*k+9,q+2,b-3)


def duration(s: L) -> int:
    a, q, b = s.a, s.q, s.b
    if a%3 == 2:
        k = a//3
        return 12*k*k+49*k+40
    k = a//3-1
    if a%3 == 0:
        if q == 0: return 12*k*k+49*k+44
        u = q-1; r = (b+1)//3; d = u+4*r; m = 4*k+3
        P = 12*k*k+41*k+32
        C = 2*u+r*(6*(m+u)+41)+12*r*(r-1)
        c = 6 if (b+1)%3 == 0 else 10 if (b+1)%3 == 1 else 16
        return P+C+2*(m+d)+c
    if q == 0: return 12*k*k+49*k+50
    if b == 0: return 12*k*k+49*k+50+4*q
    if b == 1: return 12*k*k+49*k+(96 if q == 1 else 56+4*q)
    return 12*k*k+49*k+52+6*q


def slope(s: L) -> int:
    a,q,b=s.a,s.q,s.b
    k=a//3 if a%3 == 2 else a//3-1
    return 24*k+49+(24*((b+1)//3) if a%3 == 0 and q else 0)


def trace(s: L, n: int) -> tuple[L, int] | None:
    cost=0
    for _ in range(n):
        cost+=duration(s)
        t=nxt(s)
        if t is None: return None
        s=t
    return s,cost


def linear(s: L, n: int) -> int:
    total=0
    for j in range(n):
        total+=8**j*3**(n-j-1)*slope(s)
        s=nxt(s)
        assert s is not None
    return total


def main() -> None:
    rng=random.Random(20261104)
    passed=0
    for i in range(2000):
        s=L(rng.randint(2,200),rng.randint(0,9),rng.randint(0,12))
        if s.q == 0: s=L(s.a,0,0)
        n=rng.randint(0,9)
        result=trace(s,n)
        if result is None: continue
        t,cost=result
        qcoeff=12*(64**n-9**n)//55
        for p in (0,1,2,7):
            lifted=trace(L(s.a+3**n*p,s.q,s.b),n)
            assert lifted is not None
            out,total=lifted
            assert out==L(t.a+8**n*p,t.q,t.b)
            assert total==cost+linear(s,n)*p+qcoeff*p*p
            passed+=1
    print(f"PASS: {passed} independent endpoint/time checks (seed 20261104)")
    print("Q[0..7]:", [12*(64**n-9**n)//55 for n in range(8)])


if __name__=="__main__":
    main()
