#!/usr/bin/env python3
"""Finite regression for the F119 congruence-saturation theorem.
Only a sufficient set of generic h branches is constructed; no terminal or
power edges are used. Strong connectivity is checked by two graph searches.
This is a regression, not the universal proof or a raw-machine decision.
"""
from collections import deque
import argparse


def factor_2_3(m):
    a = b = 0
    while m % 3 == 0:
        a += 1
        m //= 3
    while m % 2 == 0:
        b += 1
        m //= 2
    return a, b, m


def order3(q):
    if q == 1:
        return 1
    p = 3 % q
    k = 1
    while p != 1:
        p = 3 * p % q
        k += 1
    return k


def graph(m):
    a, b, q = factor_2_3(m)
    hstar = 2 * order3(q) - 1
    hs = sorted(set(range(a + 1)) | {hstar})
    out = [set() for _ in range(m)]
    rev = [set() for _ in range(m)]
    for h in hs:
        p = pow(3, h, m)
        for t in range(m):
            for r in (1, 2):
                x = p * (3*t+r) % m
                y = ((3*p+1)*t+p*r+h+3+(r==2)) % m
                out[x].add(y)
                rev[y].add(x)
    return out, rev


def reachable(g, x=0):
    seen = {x}
    todo = deque([x])
    while todo:
        for y in g[todo.popleft()]:
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return len(seen)


def main(limit):
    edges = 0
    for m in range(1, limit+1):
        out, rev = graph(m)
        assert reachable(out) == reachable(rev) == m, m
        edges += sum(map(len, out))
    print(f"Strongly connected for all moduli 1..{limit}; {edges} distinct directed edges across graphs.")


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--limit', type=int, default=1024)
    main(p.parse_args().limit)
