#!/usr/bin/env python3
"""Exploratory exact ResetParent reverse-cone scan for n = 887 + 13122*r.

The inverse equations are transcribed from CascadeResetInverse.ResetParent in
im-results/agent10-cascade/FirstInverseComplete.lean. This is a discovery aid,
not a replacement for a Lean proof.
"""
from collections import deque


def z2(n: int) -> int:
    p = 1 << (n - 2)
    T = 80 * p - 4118 * n - 6123
    assert T % 729 == 486, (n, T % 729)
    return 12 * (T // 243) - (2 * p + n + 1)


def even_parent(u: int, k: int) -> int:
    p = 1 << k
    assert 6 * p - 1 <= u <= 8 * p - 3
    h = 2 * u - 8 * p - k
    assert h >= 0
    return h


def odd_parent(u: int, k: int, t: int) -> int:
    N = 2 * u + 5
    m = 3 ** (t + 1)
    assert N % m == 0
    d = N // m
    assert d % 2 == 1
    v = (1 << t) * d
    p = 1 << k
    assert 6 * p + 1 <= v <= 8 * p - 1
    h = 2 * v - 8 * p - k - 5
    assert h >= 0
    return h


def band_scale(x: int) -> int:
    """The dyadic band forces k = bit_length(x)-3."""
    return x.bit_length() - 3


def parents(u: int):
    out = []
    k = band_scale(u)
    if k >= 0 and 6 * (1 << k) - 1 <= u <= 8 * (1 << k) - 3:
        out.append((2 * u - 8 * (1 << k) - k, ("even", k)))

    N = 2 * u + 5
    d = N // 3
    t = 0
    while N % 3 == 0:
        if d % 2 == 1:
            v = (1 << t) * d
            k = band_scale(v)
            if k >= 0 and 6 * (1 << k) + 1 <= v <= 8 * (1 << k) - 1:
                h = 2 * v - 8 * (1 << k) - k - 5
                if h >= 0:
                    out.append((h, ("odd", k, t)))
        N = d
        d = N // 3
        t += 1

    seen = set()
    unique = []
    for h, witness in out:
        if h not in seen:
            seen.add(h)
            unique.append((h, witness))
    return unique


def reverse_cone(root: int):
    seen = {root}
    depth = {root: 0}
    edges = []
    queue = deque([root])
    while queue:
        u = queue.popleft()
        for h, witness in parents(u):
            edges.append((u, h, witness))
            if h not in seen:
                seen.add(h)
                depth[h] = depth[u] + 1
                queue.append(h)
    return seen, edges, max(depth.values(), default=0)


def common_feeder_h(n: int) -> int:
    """Follow z2 -> four even parents -> two t=0 odd parents."""
    u = z2(n)
    for _ in range(4):
        u = even_parent(u, n - 4)
    u = odd_parent(u, n - 5, 0)
    u = odd_parent(u, n - 6, 0)
    return u


def v3(x: int) -> int:
    assert x > 0
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v


def scan(r_values):
    for r in r_values:
        n = 887 + 13122 * r
        root = z2(n)
        h = common_feeder_h(n)
        F = 463 * (1 << (n - 2)) - 8517418 * n - 12409413
        assert F == 729 * (2 * h + 5), (r, n)
        cone, edges, max_depth = reverse_cone(root)
        odd_h_parents = [w for _, w in parents(h) if w[0] == "odd"]
        print(
            f"r={r:>3} n={n:<8} nodes={len(cone):>3} edges={len(edges):>3} "
            f"depth={max_depth:>2} v3(2h+5)={v3(2*h+5):>2} "
            f"h-odd-parents={odd_h_parents}"
        )


if __name__ == "__main__":
    scan(range(21))
