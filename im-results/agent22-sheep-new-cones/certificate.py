#!/usr/bin/env python3
"""Exact all-exponent inverse-basin certificates for six Sheep E targets.

Pure Python 3.10+ standard library. Mathematical induction for all large
valuations and exceptional branches is given in the accompanying README.
The checked integer assertions provide complete periodic finite premises.
"""
from functools import lru_cache
from itertools import combinations
from math import gcd

CASES = ((194, 24300), (366, 8100), (374, 8100),
         (482, 43740), (495, 43740), (819, 14580))
PRIOR = tuple((r, 4860) for r in (138, 402, 1218, 1738)) + (
    (118, 14580), (246, 24300), (558, 8100), (846, 8100), (702, 11340))


def v2(n):
    return (n & -n).bit_length() - 1


def v3(n):
    k = 0
    while n % 3 == 0:
        k += 1
        n //= 3
    return k


def F(x):
    a = v2(x)
    u = x >> a
    assert x >= 6 and u >= 3
    return x + a + (3 if u == 3 else (u - 1) // 2)


def E(x):
    assert x >= 6 and x % 2 == 0
    z = F(x)
    h = v2(z - 1)
    return 1 + 3**h * ((z - 1) >> h)


@lru_cache(None)
def order2(modulus):
    assert modulus % 2 == 1 and modulus > 0
    if modulus == 1:
        return 1
    residue = 2 % modulus
    order = 1
    while residue != 1:
        residue = 2 * residue % modulus
        order += 1
    assert pow(2, order, modulus) == 1
    return order


def parents(y):
    """Complete genuine even-source inverse enumeration at one exact integer."""
    assert y >= 6 and y % 2 == 0
    result = []
    for h in range(v3(y - 1) + 1):
        z = 1 + (1 << h) * ((y - 1) // 3**h)
        for a in range(1, z.bit_length()):
            special = 3 << a
            if special < y and F(special) == z:
                assert E(special) == y
                result.append((special, h, a, True))
            numerator = 2*z - 2*a + 1
            v, remainder = divmod(numerator, (1 << (a+1)) + 1)
            if remainder == 0 and v >= 5 and v % 2 == 1:
                x = v << a
                if x < y:
                    assert E(x) == y
                    result.append((x, h, a, False))
    return sorted(set(result))


def child(node, h, a):
    s, b, d = node
    return (s+a+h+1,
            2**(a+h+1)*(b-d) + 2**a*d*3**h*(3-2*a),
            d*3**h*(2**(a+1)+1))


def value(node, j):
    s, b, d = node
    numerator = 2**(j+s)+b
    assert numerator % d == 0
    return numerator // d


def exact_cone(j):
    nodes = [(0,0,1)]
    edges = []
    for i, node in enumerate(nodes):
        y = value(node, j)
        for x,h,a,special in parents(y):
            assert not special, (j,i,"exceptional base predecessor",x)
            next_node = child(node,h,a)
            assert value(next_node,j)==x
            if next_node not in nodes:
                nodes.append(next_node)
            edges.append((i,h,a,nodes.index(next_node)))
        assert len(nodes) <= 20, (j,"unexpectedly large cone")
    return nodes,edges


def check(j, period):
    nodes,edges = exact_cone(j)
    assert len(edges) == len(nodes)-1
    edges_by_node = {i:{(h,a) for src,h,a,dst in edges if src==i}
                     for i in range(len(nodes))}
    for i,node in enumerate(nodes):
        s,b,d = node
        assert s >= 0 and d > 0 and d % 2 == 1 and b % 2 == 0
        assert value(node,j)>10 and value(node,j)%2==0
        assert pow(2,period,d)==1%d
        for other in nodes[:i]:
            s0,b0,d0=other
            slope=2**s*d0-2**s0*d
            offset=b*d0-b0*d
            at_j=slope*2**j+offset
            assert at_j!=0
            assert slope==0 or (at_j>0)==(slope>0)
    for src,h,a,dst in edges:
        assert src < dst
        assert child(nodes[src],h,a)==nodes[dst]
        s,b,d=nodes[src];t,c,e=nodes[dst]
        slope=2**s*e-2**t*d
        offset=b*e-c*d
        assert slope>=0 and slope*2**j+offset>0
        for k in (0,1):
            exponent=j+period*k
            x=value(nodes[dst],exponent)
            y=value(nodes[src],exponent)
            assert E(x)==y and v2(x)==a and v2(F(x)-1)==h
    rows=representatives=exceptional_cases=0
    for i,(s,b,d) in enumerate(nodes):
        Y=value((s,b,d),j)
        H=v3(Y-1)+1
        high_mod=d*3**H
        assert (pow(2,j+s,high_mod)+b-d)%high_mod!=0
        assert pow(2,period,high_mod)==1
        actual=set()
        for h in range(H):
            D=d*3**h
            C=2**h*(b-d)+D
            S=s+h
            e=(3*D).bit_length()-1
            g=e-S
            assert g>=0 and j>=g+1
            L=3*D-2**e
            U=2**(e+1)-3*D
            assert L>0 and U>0
            assert L*2**j>2**g*C
            assert U*2**j>2**(g+1)*(D*(j+3)-C)
            assert U*2**j>=2**(g+1)*D
            exceptional_cases+=1
            def K(a):return D*(2*a-1)-2*C
            A=1
            while not (1<K(A)<2**A and 2**A>=2*D):
                A+=1
            assert K(A)%2==1
            for a in range(1,A):
                m=D*(2**(a+1)+1)
                order=order2(m)
                q=order//gcd(order,period)
                assert pow(2,period*q,m)==1
                matches=[k for k in range(q)
                         if pow(2,j+S+1+period*k,m)==K(a)%m]
                if (h,a) in edges_by_node[i]:
                    assert len(matches)==q, (j,i,h,a,m,matches)
                    actual.add((h,a))
                else:
                    assert not matches, (j,i,h,a,m,matches)
                rows+=1
                representatives+=q
        assert actual==edges_by_node[i]
    return len(nodes),len(edges),rows,representatives,exceptional_cases


def main():
    for (j,p),(r,q) in combinations(CASES,2):
        assert (j-r)%gcd(p,q)!=0
    for j,p in CASES:
        for r,q in PRIOR:
            assert (j-r)%gcd(p,q)!=0
        n,e,rows,reps,special=check(j,p)
        print(f"PASS {j}+{p}k: {n} nodes, {e} edges, {rows} low-a rows, "
              f"{reps} periodic representatives, {special} exceptional gaps")
    print("PASS: all six exact inverse cones; pairwise disjoint, "
          "disjoint from nine earlier E progressions")


if __name__ == "__main__":
    main()
