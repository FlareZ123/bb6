#!/usr/bin/env python3
"""All-hidden-length H4 leaf classification; pure Python integer arithmetic."""
from math import gcd, lcm
from fractions import Fraction

# (hidden length, source valuation, odd exponent-parameter residue, period)
CLASSES = [
    (0,2,3,18), (0,4,25,30), (1,2,5,54), (2,2,89,162),
    (3,2,215,486), (3,3,107,108), (3,4,269,810),
    (4,2,1133,1458), (4,6,3239,3402), (5,2,323,4374),
    (5,6,2753,10206), (6,2,10043,13122), (7,3,2753,8748)
]

def v3(n):
    assert n > 0
    h = 0
    while n % 3 == 0:
        n //= 3
        h += 1
    return h

def residues(h, b):
    q = 2**(b+1)+1
    m = 3**(h+7)*q
    k = 2**(h+1)*4055 + 3**(h+7)*(2*b-3)
    p = lcm(2, 3**(h+v3(q)), 2*(b+1)//gcd(2*(b+1),1458))
    g = pow(2,1458,m)
    assert pow(g,p,m) == 1
    v = initial = pow(2,1212+h,m)
    out = []
    for r in range(p):
        if r%2 == 1 and v == k%m:
            out.append(r)
        v = v*g%m
    assert v == initial
    return p,out

def exact_witness(r,h,b):
    a = 1201+1458*r
    y,rem = divmod(2**(a+10)-1868,2187)
    assert rem == 0
    w,rem = divmod(y-1,3**h)
    assert rem == 0 and w%2 == 1
    v,rem = divmod(2*(1+2**h*w)+1-2*b,2**(b+1)+1)
    assert rem == 0 and v>=5 and v%2 == 1
    x = 2**b*v
    f = x+b+(v-1)//2
    assert f-1 == 2**h*w and 1+3**h*w == y
    return (r,a,v3(y-1),h,b,x.bit_length())

def main():
    assert pow(2,1211,2187) == 1868
    assert pow(2,1458,2187) == 1
    # The two base inequalities propagate by the elementary induction in README.
    assert 1 < 2*4055 + 2187*31 < 2**17
    assert 2*2187 < 2**17
    hits = []
    # Crucial: enumerate all h <= 6 without any exact v3(y-1)=h filter.
    for h in range(7):
        for b in range(1,2*h+17):
            p,rr = residues(h,b)
            hits.extend((h,b,r,p) for r in rr)
    assert hits == CLASSES[:-1], hits
    assert residues(7,3) == (8748,[2753])
    # If v3(y-1)>=7, use one of h=3 or h=7 with b=3.
    m = 3**14
    assert pow(2,1458*2187,m) == 1
    rr = [r for r in range(2187) if pow(2,1211+1458*r,m)==4055%m]
    assert rr == [566], rr
    assert 566%27 == 26 and 107%27 == 26 and 107%4 == 3
    assert 2753%2187 == 566 and 2753%4 == 1
    # The exceptional-source bound independently covers every hidden length.
    assert (2187+1868)*((27+2)**3+27+2)<2**27
    assert 2187*(1+(3*2**27+27+2)**2)+1868<2**69
    p=lcm(*(row[3] for row in CLASSES))
    flags=bytearray([1])*p
    flags[::2]=bytes(p//2)
    for h,b,r,q in CLASSES:
        flags[r::q]=bytes(p//q)
    assert p==918540
    assert sum(flags)==344240
    density=Fraction(sum(flags),p)
    assert density==Fraction(17212,45927)
    assert density/1458==Fraction(8606,33480783)
    print("complete odd-r leaf density",density,"exponent density",density/1458)
    # Disjointness from the prior 158/243 classes in Agent16's note.
    prior = [(72,[17,23,35,41,59,71]),(120,[9,15,27,39,51,57,75,81,87,99,105,111]),
             (20,[0,12,16]),(216,[7,19,43,55,79,115,127,151,163,187]),
             (648,[31,139,211,247,319,355,463,535,571,643]),
             (1944,[175,283,499,607,823,1147,1255,1471,1579,1795]),(4,[2])]
    for m,rs in prior:
        # Every prior a-class pulls back to a class of r modulo m/gcd(m,1458).
        # That modulus divides the common period p.
        g=gcd(m,1458)
        q=m//g
        assert p%q==0
        for s in rs:
            if (s-1201)%g==0:
                r0=((s-1201)//g*pow(1458//g,-1,q))%q
                assert not any(flags[r0::q]),(m,s,r0,q)
    print("disjoint combined density",Fraction(158,243)+density/1458)
    print("counterexample:",exact_witness(3239,4,6))
    print("counterexample:",exact_witness(20249,7,3))

if __name__=="__main__":
    main()
