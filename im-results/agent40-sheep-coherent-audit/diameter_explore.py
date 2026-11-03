"""Exhaustive finite directed diameter of the generic Sheep dyadic quotient.

Each edge is algebraically characterized by Agent22's complete inverse map.
All-modulus directed diameter formula is conjectural beyond these finite p.
"""
from collections import Counter, deque


def parent(p: int, a: int, h: int, s: int) -> int:
    m = 1 << (p-a)
    d = 1+(1 << (a+1))
    u = ((3-2*a+(1 << (h+1))*pow(3**h,-1,m)*(s-1))*pow(d,-1,m)) % m
    return (1 << a)*u


def check(p: int) -> tuple[int, Counter]:
    assert 1 <= p <= 12
    n = 1 << (p-1)
    neighbors = [set() for _ in range(n)]
    for s in range(0,2*n,2):
        neighbors[0].add(s//2)
        for a in range(1,p):
            for h in range(p-a):
                neighbors[parent(p,a,h,s)//2].add(s//2)
    graph = [list(x) for x in neighbors]
    diameter = 0
    ecc = Counter()
    for r in range(n):
        dist = [-1]*n
        dist[r] = 0
        todo = deque([r])
        while todo:
            v = todo.popleft()
            for w in graph[v]:
                if dist[w] < 0:
                    dist[w] = dist[v]+1
                    todo.append(w)
        assert all(v>=0 for v in dist)
        e = max(dist)
        ecc[e] += 1
        diameter = max(diameter,e)
    return diameter,ecc


if __name__ == '__main__':
    for p in range(1,12):
        d, ecc = check(p)
        assert d == p//2
        print(f'p={p}, vertices={1 << (p-1)}, diameter={d}, eccentricity_distribution={dict(ecc)}',flush=True)
    print('PASS exact directed diameters p=1..11 agree with floor(p/2)')
