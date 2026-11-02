"""Exact all-exponent modular certificate for the Sheep even-return map.

The verified theorem is that the genuine even orbit starting at 10 misses every
2^(138 + 4860*k), k>=0. Requires only Python 3.10+ standard library.
The accompanying README supplies the proof that these finite modular tests
exhaust all possible even-return predecessors.
"""
from dataclasses import dataclass
from functools import lru_cache
from math import gcd, lcm

R = 138
M = 4860


@dataclass(frozen=True)
class Node:
    s: int
    b: int
    d: int
    H: int
    limits: tuple
    n0: tuple


ROOT = Node(0, 0, 1, 3, (2, 5, 7), (6, 7, 10))
P1 = Node(3, -2, 15, 4, (8, 10, 12, 14), (11, 15, 18, 21))
P2 = Node(5, -68, 81, 2, (11, 13), (16, 19))


@lru_cache(None)
def factors(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


@lru_cache(None)
def period2(d):
    """Exact multiplicative order of 2 modulo positive odd d."""
    assert d > 0 and d % 2 == 1
    if d == 1:
        return 1
    phi = d
    for p in factors(d):
        phi = phi // p * (p - 1)
    result = phi
    for p in factors(phi):
        while result % p == 0 and pow(2, result // p, d) == 1:
            result //= p
    assert pow(2, result, d) == 1
    for p in factors(result):
        assert pow(2, result // p, d) != 1
    return result


def cycle_modulus(d):
    return period2(d) // gcd(period2(d), M)


def verify_mod_zero(d, s, b):
    """All k in a complete period where 2^(R+Mk+s)+b = 0 modulo d."""
    return tuple(k for k in range(cycle_modulus(d))
                 if (pow(2, R + M*k + s, d) + b) % d == 0)


def exceptional_bound(D, C, n):
    """An all-n>=n0 bound excluding z=3*2^a+a+3, for any a>=1."""
    c = 3 * D
    e = c.bit_length()
    assert (1 << (e-1)) < c < (1 << e)
    assert n >= e+2
    assert (((1 << e)-c) << (n-e)) > D*(n+3)+abs(C)
    assert (1 << (n-e)) > 2*D
    assert D*(n-e+4) >= C


def gap_bound(D, C, a):
    """For every a>=A, 1<Q_a<2^a, Q_a=D(2a-1)-2C odd."""
    q = D*(2*a-1)-2*C
    assert q % 2 == 1 and 1 < q < (1 << a) and (1 << a) > 2*D


def eligible_k(node, h, a):
    D = node.d * 3**h
    C = (1 << h)*(node.b-node.d) + D
    den = D*((1 << (a+1))+1)
    b1 = 2*C-D*(2*a-1)
    period = lcm(period2(D), period2(den))
    cycle = period // gcd(period, M)
    good = []
    for k in range(cycle):
        j = R + M*k
        hvalid = (pow(2, j+node.s, D)+node.b-node.d) % D == 0
        # For positive exponent, period modulo 2*den equals order modulo den.
        oddquotient = (pow(2, j+node.s+h+1, 2*den)+b1) % (2*den) == den
        if hvalid and oddquotient:
            good.append(k)
    child = (node.s+h+1+a, (1 << a)*b1, den)
    return good, child, cycle


def verify_node(node, expected):
    print("NODE", node)
    # h >= H requires 3^H | (Y-1). This finite test excludes it for all k.
    assert not verify_mod_zero(node.d*3**node.H, node.s, node.b-node.d)
    actual = {}
    for h, (A,n0) in enumerate(zip(node.limits, node.n0)):
        D = node.d*3**h
        C = (1 << h)*(node.b-node.d)+D
        exceptional_bound(D, C, n0)
        assert R+node.s+h >= n0
        gap_bound(D, C, A)
        for a in range(1, A):
            good, child, cycle = eligible_k(node,h,a)
            if good:
                actual[(h,a)] = child
                print("  surviving h,a",h,a,"child",child,
                      "offsets",good,"period",cycle)
    assert actual == expected, (actual,expected)


def main():
    verify_node(ROOT, {(1,1):(3,-2,15), (2,2):(5,-68,81)})
    verify_node(P1, {})
    verify_node(P2, {})
    # Each rational symbolic node is genuinely integral at every allowed j,
    # via the same fixed exponent congruence period.
    for node in (ROOT,P1,P2):
        period = cycle_modulus(node.d)
        assert all(((1 << (R+M*k+node.s))+node.b) % node.d == 0
                   for k in range(period))
        assert ((1 << (R+node.s))+node.b)//node.d > 10
    print("PASS: all infinite-index modular cases and bounds checked.")
    print("No E-reachable 2^(138+4860*k) from initial 10, for any k>=0.")


if __name__ == "__main__":
    main()
