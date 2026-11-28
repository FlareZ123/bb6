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

def multiplicative_order(a, modulus):
    """Brute-force exact order, bounded by the modulus (all orders <=262146)."""
    assert gcd(a, modulus) == 1
    x=1
    for k in range(1,modulus+1):
        x=x*a % modulus
        if x==1:
            return k
    raise AssertionError((a,modulus))

def all_pair_orders():
    result={}
    for v in W:
        for w in W:
            if v==w: continue
            assert gcd(D(v),D(w))==1
            modulus=D(w)//gcd(D(w),d(w)-d(v))
            ratio=D(v)*pow(2**(v+1),-1,modulus) % modulus
            result[(v,w)]=multiplicative_order(ratio,modulus)
    assert len(result)==42
    assert result[3,5]==11 and result[5,3]==18
    assert result[3,17]==262146 and result[14,4]==3
    print('All 42 exact return periods, rows v and columns w:')
    for v in W:
        print('v=',v, {w:result[v,w] for w in W if w!=v})
    return result

def affine_residue_step(v, w, residue):
    """Necessary/sufficient odd-modulus transfer for a genuine v-edge."""
    M=D(w)
    return (pow(D(v), -1, M)*(2**(v+1)*residue+3*(d(w)-d(v))))%M

def restricted_valuation_return():
    """Exact reachable-residue frontier for inverse words avoiding w."""
    all_results={}
    for w in W:
        residues={0}
        sizes=[1]
        first=None
        for k in range(1,9):
            residues={affine_residue_step(v,w,z)
                      for z in residues for v in W if v!=w}
            sizes.append(len(residues))
            if 0 in residues:
                first=k
                break
        all_results[w]=(first,sizes)
    assert all_results[14]==(7,[1,6,36,216,1278,6962,24940,32765])
    assert all_results[17][0]==5
    print('restricted mixed-word first returns and frontier sizes:',all_results)
    # Source-faithful explicit 7-edge return witness for valuation 14.
    x=99417925155886663006208
    B=x
    for v in (11,3,4,17,6,4,6):
        assert B%2**v==0
        t=B//2**v
        assert t>=3 and t%2==1
        B=B+v+3*((t-3)//2+1)
    assert B==148040327779734176791202
    assert available(x,14) and available(B,14)
    print('w14 first mixed return at length 7: start',x,'target',B)
    return all_results

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
    all_pair_orders()
    restricted_valuation_return()
    print('PASS')

if __name__ == '__main__':
    audit()
