#!/usr/bin/env python3
"""Exact arithmetic regression for mixed-valuation Space Needle inverse paths.
No root-orbit or BB(6) conclusion is asserted.
"""
from math import gcd

W = (3, 4, 5, 6, 11, 14, 17)
D = lambda w: 2**(w+1) + 3
d = lambda w: 2**w * (2*w-3)

def crt(a, m, b, n):
    assert gcd(m, n) == 1
    return (a + m * (((b-a) * pow(m, -1, n)) % n)) % (m*n)

def parent(B, w):
    c = 3*2**w + w + 3
    assert B >= c and (B-c) % D(w) == 0, (w,B)
    q = (B-c)//D(w)
    p = 2**w*(2*q+3)
    assert p+w+3*(q+1) == B
    return p

def available(B, w):
    return B >= 3*2**w+w+3 and (3*B+d(w))%D(w)==0

def audit():
    # Every pair of distinct source valuations in W has a modular gap:
    # any target with both incoming edges forbids a switch at the first
    # ancestor; proof by the affine cross-potential identity in README.
    gaps = {}
    for v in W:
        for w in W:
            if v == w:
                continue
            r = (3*(d(w)-d(v)))%D(w)
            assert r != 0
            gaps[(v,w)] = r
    assert len(gaps)==42
    print('42/42 directed immediate-switch gaps nonzero')

    # The exact modular resonance for 3-arm -> 5-parent is 11.
    assert pow(-3,11,67)==1
    assert all(pow(-3,j,67)!=1 for j in range(1,11))
    B = crt(-8 % 19**11, 19**11, (-224*pow(3,-1,67))%67, 67)
    assert available(B,3) and available(B,5)
    cur=B
    for j in range(1,12):
        cur=parent(cur,3)
        assert available(cur,5) == (j%11==0)
    assert B==6639944757198475 and cur==1002754604531704
    print('3->5 resonance: first possible mixed edge depth 11, B=',B)

    # The opposite direction resonates for the first time at depth 18.
    assert pow(-4,18,19)==1
    assert all(pow(-4,j,19)!=1 for j in range(1,18))
    modulus=67**18
    B=crt((-224*pow(3,-1,modulus))%modulus, modulus,
          (-24*pow(3,-1,19))%19, 19)
    assert available(B,5) and available(B,3)
    cur=B
    for j in range(1,19):
        cur=parent(cur,5)
        assert available(cur,3) == (j%18==0)
    print('5->3 resonance: first possible mixed edge depth 18, B=',B)
    print('PASS')

if __name__ == '__main__':
    audit()
