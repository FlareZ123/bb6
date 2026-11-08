#!/usr/bin/env python3
"""Exhaustive finite CountCone search for the exceptional right-five endpoint.

The transition equations are the arithmetic characterization supplied by
P1FiniteInverse.inverseAt_iff_power_mass:

    d + b/2 + 3 = 2^t * (c + 3)
    2*k + c + 2*t + 1 + (c % 2) = b + d

with the CountCone parent guards b >= 8, b % 4 = 0, d odd, k >= 2,
and c odd. The child is (2*k - 4, c + 4).

For fixed n, the root is (14*2^n - 2*n - 16, 3). The mass invariant
b + d + 2*m = 14*2^n - 2*n - 13 makes m unique for each (b,d), so
deduplicating states by (b,d) is exact for endpoint reachability. Every
edge decreases b+d by 2*(t+1), hence the state graph is finite.

A completed search with no hit proves that this fixed-n CountCone tree has
no endpoint with d=5. A capped search is only partial evidence.
"""

from __future__ import annotations

import argparse
import json
from typing import Any


def inverse_children(b: int, d: int):
    """Yield (child_b, child_d, t, k, c) for every legal CountCone parent."""
    if b < 8 or b % 4 != 0 or d % 2 != 1:
        return

    a = d + b // 2 + 3
    # c is odd iff a / 2^t is even, so t < v2(a).
    v2 = (a & -a).bit_length() - 1
    for t in range(v2):
        q = a >> t
        c = q - 3
        if c < 1 or c % 2 != 1:
            continue

        numerator = b + d - c - 2 * t - 2
        if numerator < 0 or numerator % 2 != 0:
            continue
        k = numerator // 2
        if k < 2:
            continue

        yield 2 * k - 4, c + 4, t, k, c


def search(n: int, max_states: int) -> dict[str, Any]:
    if n < 14:
        raise ValueError("the source family is stated for n >= 14")
    p = 1 << n
    root = (14 * p - 2 * n - 16, 3)
    initial_mass = root[0] + root[1]

    stack = [root]
    seen = {root}
    # child -> (parent_b, parent_d, t, k, c)
    parent: dict[tuple[int, int], tuple[int, int, int, int, int]] = {}
    found: tuple[int, int] | None = None

    while stack:
        b, d = stack.pop()
        if d == 5:
            found = (b, d)
            break

        for child_b, child_d, t, k, c in inverse_children(b, d):
            child = (child_b, child_d)
            if child in seen:
                continue
            seen.add(child)
            parent[child] = (b, d, t, k, c)
            stack.append(child)
            if len(seen) >= max_states:
                return {
                    "n": n,
                    "found": False,
                    "complete": False,
                    "states": len(seen),
                    "reason": "max_states reached",
                }

    path: list[dict[str, int]] = []
    if found is not None:
        cur = found
        while cur != root:
            pb, pd, t, k, c = parent[cur]
            path.append({
                "from_b": pb,
                "from_d": pd,
                "to_b": cur[0],
                "to_d": cur[1],
                "t": t,
                "k": k,
                "c": c,
            })
            cur = (pb, pd)
        path.reverse()

    m = sum(step["t"] + 1 for step in path)
    z = sum(step["t"] > 0 for step in path)
    final_b, final_d = found if found is not None else (None, None)
    if found is not None:
        assert final_d == 5
        assert final_b + final_d + 2 * m == initial_mass
        assert z <= len(path)

    return {
        "n": n,
        "found": found is not None,
        "complete": True,
        "states": len(seen),
        "path_length": len(path),
        "cost_m": m if found is not None else None,
        "positive_depth_resets_z": z if found is not None else None,
        "path": path if found is not None else [],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--max-states", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.max_states), indent=2))


if __name__ == "__main__":
    main()
