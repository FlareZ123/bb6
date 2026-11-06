"""Exact small-modulus all-pairs audit and symbolic lower-witness test.

Only standard-library Python. The finite h cutoff is complete: for odd q,
(3/2)^h mod q has preperiod <=v3(q), then period dividing Euler phi(q/3^e).
Beyond the dyadic inverse gate saturation threshold, repeating that odd value
repeats the exact quotient edge. This checks the ENTIRE finite generic graph
at each chosen (p,q); it is not a proof for unbounded p or q, which is in
MIXED-EXACT-DIAMETER.md.
"""
from collections import deque
from math import gcd


def phi(n: int) -> int:
    result = n
    d = 2
    while d*d <= n:
        if n % d == 0:
            while n % d == 0:
                n //= d
            result = result//d*(d-1)
        d += 1
    if n > 1:
        result = result//n*(n-1)
    return result


def h_cutoff(p: int, q: int) -> int:
    e = 0
    n = q
    while n % 3 == 0:
        n //= 3
        e += 1
    return max(p,e) + phi(n) + 2


def lower_witness(p: int, q: int) -> tuple[int, int] | None:
    assert p >= 1 and q >= 1 and q%2 == 1
    if q == 1:
        return None
    M = 2**p
    k = p//2
    if p == 1:
        return (0,2)
    if p%2 == 1:
        rq = 0
        z = rq
        for _ in range(k):
            z = ((5*z+2)*pow(4,-1,q))%q
        sq = (z+1)%q
    elif gcd(5,q) == 1:
        rq = 1
        for _ in range(k):
            rq = ((4*rq-2)*pow(5,-1,q))%q
        sq = 0
    else:
        rq = 0
        sq = 1
    r2 = M-2
    s2 = 0
    r = r2+M*((rq-r2)*pow(M,-1,q)%q)
    s = s2+M*((sq-s2)*pow(M,-1,q)%q)
    assert 0 <= r < M*q and 0 <= s < M*q
    assert r%2 == 0 and s%2 == 0 and r != s
    return (r,s)


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length()-1


def dyadic_parent(p: int, a: int, h: int, s: int) -> int:
    M = 2**(p-a)
    D = 1+2**(a+1)
    u = ((3-2*a+2**(h+1)*pow(3**h,-1,M)*(s-1))
         *pow(D,-1,M))%M
    return 2**a*u


def full_generic_graph(p: int, q: int) -> dict[int, set[int]]:
    M = 2**p
    nodes = list(range(0,M*q,2))
    outgoing = {r:set() for r in nodes}
    H = h_cutoff(p,q)
    for r in nodes:
        if r%M == 0:
            outgoing[r].update(nodes)
            continue
        a = v2(r%M)
        if a == 1:
            f_q = ((5*r+2)*pow(4,-1,q))%q
        else:
            u_q = r*pow(2,-a,q)%q
            f_q = (r+a+(u_q-1)*pow(2,-1,q))%q
        for h in range(H):
            hs = min(h,p-a-1)
            sq = (1+pow(3,h,q)*pow(2,-h,q)*(f_q-1))%q
            for s2 in range(0,M,2):
                if dyadic_parent(p,a,hs,s2) != r%M:
                    continue
                target = s2+M*((sq-s2)*pow(M,-1,q)%q)
                outgoing[r].add(target)
    return outgoing


def distances(outgoing: dict[int,set[int]], start: int) -> dict[int,int]:
    d = {start:0}
    queue = deque([start])
    while queue:
        x = queue.popleft()
        for y in outgoing[x]:
            if y not in d:
                d[y] = d[x]+1
                queue.append(y)
    return d


def verify() -> None:
    total_vertices = 0
    total_moduli = 0
    for p in range(1,9):
        for q in (1,3,5,7,9,11,15,21):
            if q*2**(p-1) > 400:
                continue
            graph = full_generic_graph(p,q)
            expected = p//2 + int(q>1)
            witness = lower_witness(p,q)
            if witness is not None:
                r,s = witness
                observed = distances(graph,r)[s]
                assert observed == expected, (p,q,r,s,observed)
            diameter = max(max(distances(graph,r).values()) for r in graph)
            assert diameter == expected, (p,q,diameter,expected)
            total_vertices += len(graph)
            total_moduli += 1
            print(f"PASS p={p}, q={q}, diameter={diameter}, lower={witness}",flush=True)
    print(
        f"PASS {total_moduli} complete finite generic quotient graphs, "
        f"{total_vertices} cumulative vertices",
        flush=True,
    )


if __name__ == "__main__":
    verify()
