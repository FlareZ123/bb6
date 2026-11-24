#!/usr/bin/env python3
"""Exact parameter-level preimages of Agent22's three-return fatal family."""
from collections import Counter
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "agent49-parity623"))
from inverse623 import predecessors

def tern(t):
    n1 = n2 = 0
    while t:
        t, r = divmod(t, 3)
        n1 += r == 1
        n2 += r == 2
    return n1, n2

def bal(t):
    np = nm = 0
    while t:
        q, r = divmod(t, 3)
        np += r == 1
        nm += r == 2
        t = q + (r == 2)
    return np, nm

def find(fn, target, hi):
    lo = 0
    while lo <= hi:
        t = (lo + hi) // 2
        v = fn(t)
        if v == target:
            return t
        if v < target:
            lo = t + 1
        else:
            hi = t - 1
    return None

def parameters(p):
    assert p >= 8 and p % 2 == 0
    tL = find(lambda t: 3*t-1-2*tern(t)[0]-tern(t)[1], p, p+1)
    tR = find(lambda t: 3*t+bal(t)[0]+2*bal(t)[1]+1, 3*p, p)
    return tL, tR

def target(p):
    return (3**p-5)//2, (13*3**p-4*p+7)//2

def predicted(p):
    tL, tR = parameters(p)
    x, _ = target(p)
    B = (13*3**(p-1)-1)//2
    out = set()
    if tL is not None:
        n1, n2 = tern(tL)
        b = B-2*tL-1
        A = x-(p-4-2*(n1+n2))
        out.add((A+b, b-2))
    if tR is not None:
        _, nm = bal(tR)
        b = B-2*tR
        A = x+(p-1)-2*nm
        out.add((b+1, A+b-3))
    return out

if __name__ == "__main__":
    counts = Counter()
    for p in range(8, 2002, 2):
        pp = predicted(p)
        actual = set(predecessors(target(p), even_only=True))
        assert pp == actual, (p, pp, actual)
        counts[len(pp)] += 1
    print("Matched all even p=8..2000:", sorted(counts.items()))
