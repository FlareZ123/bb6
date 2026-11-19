#!/usr/bin/env python3
"""Exact reverse ResetParent cone for the first unresolved rho-20 class-2 example.

This is a fixed-candidate experiment, not a family theorem. It enumerates every
even parent and every admissible odd exponent t, using the source-exact bands.
Run with Python 3; no third-party packages are required.
"""

from collections import deque
from dataclasses import dataclass


@dataclass(frozen=True)
class Parent:
    kind: str
    t: int | None
    level: int
    height: int


def valuation3(n: int) -> int:
    v = 0
    while n % 3 == 0:
        n //= 3
        v += 1
    return v


def even_parent(u: int) -> Parent | None:
    # The even-child band [6*2^k-1, 8*2^k-3] lies wholly in
    # [2^(k+2), 2^(k+3)-1], so its only possible level is bit_length(u)-3.
    k = u.bit_length() - 3
    if k < 1:
        return None
    p2 = 1 << k
    if 6 * p2 - 1 <= u <= 8 * p2 - 3:
        h = 2 * u - 8 * p2 - k
        if 0 < h < u:
            return Parent("even", None, k, h)
    return None


def odd_parents(u: int) -> list[Parent]:
    x = 2 * u + 5
    v = valuation3(x)
    out: list[Parent] = []
    for t in range(v):
        d = x // (3 ** (t + 1))
        if d % 2 == 0:
            continue
        source = (1 << t) * d
        # The odd-source band [6*2^k+1, 8*2^k-1] has the same
        # unique bit-length level as the even band.
        k = source.bit_length() - 3
        if k < 1:
            continue
        p2 = 1 << k
        if 6 * p2 + 1 <= source <= 8 * p2 - 1:
            h = 2 * source - 8 * p2 - k - 5
            if 0 < h < u:
                out.append(Parent("odd", t, k, h))
    return out


def parents(u: int) -> list[Parent]:
    out = odd_parents(u)
    e = even_parent(u)
    if e is not None:
        out.append(e)
    return out


def main() -> None:
    a = 20
    gamma = 103
    k = 97 * (1 << (a - 7)) + (gamma - 7) // 2
    p = 1 << k
    r = k + 4 - a
    b = (2 * k + 7) * (1 << r)
    numerator = b - 16 * p + 2 * k + 1
    assert numerator % 3 == 0
    d = numerator // 3
    e = 8 * p + k - d

    assert k == 794672
    assert k % 6 == 2 and (k + 6 * a) % 54 == 20
    assert (2 * k + 7) * 64 >= 97 * (1 << a)
    assert 2 * k + 7 < 13 * (1 << (a - 3))
    assert valuation3(2 * e + 5) == 2

    nodes = [e]
    depths = [0]
    index = {e: 0}
    edges: list[tuple[int, int, str, int | None, int]] = []

    cursor = 0
    while cursor < len(nodes):
        u = nodes[cursor]
        for parent in parents(u):
            h = parent.height
            if h not in index:
                index[h] = len(nodes)
                nodes.append(h)
                depths.append(depths[cursor] + 1)
            edges.append(
                (cursor, index[h], parent.kind, parent.t, parent.level)
            )
        cursor += 1

    leaf_ids = [i for i, u in enumerate(nodes) if not parents(u)]
    branch_ids = [i for i, u in enumerate(nodes) if len(parents(u)) > 1]
    root_reachable = 2 in index or any(parent.height == 2 for u in nodes for parent in parents(u))
    assert len(nodes) == 35
    assert len(edges) == 34
    assert len(leaf_ids) == 8
    assert max(depths) == 14
    assert not root_reachable
    assert len({dst for _, dst, *_ in edges}) == len(nodes) - 1

    print(f"a={a} gamma={gamma} K={k} r={r}")
    print(f"E_bits={e.bit_length()} v3(2E+5)={valuation3(2 * e + 5)}")
    print(f"nodes={len(nodes)} edges={len(edges)} leaves={len(leaf_ids)}")
    print(f"max_depth={max(depths)} branch_nodes={len(branch_ids)}")
    print(f"depth_histogram={dict(sorted((d, depths.count(d)) for d in set(depths)))}")
    print(f"root_2_reachable={root_reachable}")
    print("branch_depths=" + ",".join(str(depths[i]) for i in branch_ids))


if __name__ == "__main__":
    main()
