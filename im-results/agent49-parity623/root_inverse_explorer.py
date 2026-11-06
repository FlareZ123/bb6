#!/usr/bin/env python3
"""Exploratory exact mirror and affine-ray inverse search for BB6 machine #623.

Upstream source pin:
  google-deepmind/cryptids @ c86f15861709b76042998c5211c7b2f83991621b

This file is an independently transcribed Python mirror of evalA, drainB and
highLevelNext. It is useful for reproducible finite experiments and candidate
generation. It is NOT a proof and is not used by the Lean source verification.
The source-imported statements are in TernaryShiftSource.lean,
TernaryBufferSource.lean and AffinePredecessorBoundsSource.lean.
"""

from collections import deque


def eval_a(a: int, k: int, m: int):
    """Exact iterative mirror of the upstream evalA recursion."""
    while True:
        digit = k % 3
        if digit == 2:
            return a + 1, k // 3, m
        if a == 0:
            if digit == 0:
                return None
            return 0, k // 3, m
        if digit == 0:
            return a - 1, k // 3, m + 2
        a -= 1
        m += 2 * (k // 3) + 3
        k //= 3


def drain_b(a: int, b: int, d: int):
    """Exact iterative mirror of the upstream drainB recursion."""
    while b > 0:
        result = eval_a(a, b - 1, d + 2 * b + 3)
        if result is None:
            return None
        aa, bb, dd = result
        if bb >= b:
            return None
        a, b, d = aa, bb, dd
    return a, d


def high_level_next(a: int, d: int):
    """Exact mirror of highLevelNext on D(a,d)."""
    if a == 0:
        if d % 2 == 1:
            return drain_b(d + 1, 2, 2)
        return d, 7
    if d % 2 == 1 and a >= d + 5:
        return drain_b(a - d - 5, d + 3, 5)
    if d % 2 == 0 and a >= d + 3:
        return drain_b(a - d - 2, d + 2, 2)
    if a % 2 == 1:
        return None
    if a == d + 2:
        return drain_b(0, a, 2)
    if d % 2 == 1:
        return drain_b(d + 4 - a, a - 1, 3)
    result = eval_a(d + 1 - a, a, 2 * a + 5)
    if result is None:
        return None
    return drain_b(*result)


def ones_ge(n: int, x: int) -> bool:
    """Return whether u_n=(3^n-1)/2 is at least x, without huge powers."""
    if n < 0:
        return False
    if n >= x.bit_length() + 1:
        return True
    return (3**n - 1) // 2 >= x


def ones_gt(n: int, x: int) -> bool:
    return ones_ge(n, x + 1)


def min_n_ones_ge(x: int) -> int:
    n = 0
    while not ones_ge(n, x):
        n += 1
    return n


def min_n_ones_gt(x: int) -> int:
    n = 0
    while not ones_gt(n, x):
        n += 1
    return n


def new_affine_cone(a: int, d: int) -> bool:
    """The four-sector exponential cone from TernaryBufferSource.lean."""
    return (
        (d % 2 == 1 and d + 5 <= a and ones_ge(a - d - 5, d + 3))
        or (d % 2 == 0 and d + 3 <= a and ones_ge(a - d - 2, d + 2))
        or (
            a > 0
            and a % 2 == 0
            and a <= d
            and d % 2 == 1
            and ones_ge(d + 4 - a, a - 1)
        )
        or (
            a > 0
            and a % 2 == 0
            and a <= d
            and d % 2 == 0
            and ones_gt(d + 1 - a, a)
        )
    )


def predecessors(target: tuple[int, int]) -> list[tuple[int, int]]:
    """Candidate inverse search using affine ray representatives.

    Each unbounded ray is reduced to a budget-satisfying base, with the finite
    prefix checked directly. Every candidate is rechecked by high_level_next.
    Completeness of this full enumerator remains exploratory; the Lean module
    proves the four sector envelopes, not this Python search procedure.
    """
    x, y = target
    found: set[tuple[int, int]] = set()

    # The global strict-mass theorem gives a+d <= x+y-7.
    if x + y >= 7:
        for d in range(x + y - 6):
            if high_level_next(0, d) == target:
                found.add((0, d))

    # Far-left odd: a0=d+5+n0, where u_n0 >= d+3.
    if y >= 14:
        for d in range(1, (y - 14) // 3 + 1, 2):
            n0 = min_n_ones_ge(d + 3)
            a0 = d + 5 + n0
            for a in range(d + 5, a0):
                if high_level_next(a, d) == target:
                    found.add((a, d))
            base = high_level_next(a0, d)
            if base is not None and base[1] == y and x >= base[0]:
                a = a0 + x - base[0]
                if high_level_next(a, d) == target:
                    found.add((a, d))

    # Far-left even: a0=d+2+n0, where u_n0 >= d+2.
    if y >= 8:
        for d in range(0, (y - 8) // 3 + 1, 2):
            n0 = min_n_ones_ge(d + 2)
            a0 = d + 2 + n0
            for a in range(d + 3, a0):
                if high_level_next(a, d) == target:
                    found.add((a, d))
            base = high_level_next(a0, d)
            if base is not None and base[1] == y and x >= base[0]:
                a = a0 + x - base[0]
                if high_level_next(a, d) == target:
                    found.add((a, d))

    # Special diagonal branch a=d+2.
    if y >= 8:
        for a in range(2, (y - 2) // 3 + 1):
            if high_level_next(a, a - 2) == target:
                found.add((a, a - 2))

    # Far-right odd, including the a=d+1 edge. Choose an odd base d0>=a.
    for a in range(2, y // 3 + 1, 2):
        n0 = max(5, min_n_ones_ge(a - 1))
        if n0 % 2 == 0:
            n0 += 1
        d0 = a - 4 + n0
        for d in range(a - 1, d0, 2):
            if high_level_next(a, d) == target:
                found.add((a, d))
        base = high_level_next(a, d0)
        if base is not None and base[1] == y and x >= base[0] and (x - base[0]) % 2 == 0:
            d = d0 + x - base[0]
            if high_level_next(a, d) == target:
                found.add((a, d))

    # Odd near-left gap a=d+3.
    if y >= 9:
        for d in range(1, y // 3 + 1, 2):
            a = d + 3
            if high_level_next(a, d) == target:
                found.add((a, d))

    # Far-right even. Choose an even base d0>=a.
    if y >= 9:
        for a in range(2, (y - 5) // 2 + 1, 2):
            n0 = max(1, min_n_ones_gt(a))
            if n0 % 2 == 0:
                n0 += 1
            d0 = a - 1 + n0
            for d in range(a, d0, 2):
                if high_level_next(a, d) == target:
                    found.add((a, d))
            base = high_level_next(a, d0)
            if base is not None and base[1] == y and x >= base[0] and (x - base[0]) % 2 == 0:
                d = d0 + x - base[0]
                if high_level_next(a, d) == target:
                    found.add((a, d))

    return sorted(found)


def brute_predecessors(target: tuple[int, int]) -> list[tuple[int, int]]:
    """Small-target reference enumeration using the strict-mass bound."""
    x, y = target
    bound = x + y - 7
    if bound < 0:
        return []
    out = []
    for a in range(bound + 1):
        for d in range(bound - a + 1):
            if high_level_next(a, d) == target:
                out.append((a, d))
    return out


def check_small_grid(limit: int = 60) -> bool:
    """Regression comparison of ray inversion with brute force."""
    for x in range(limit + 1):
        for y in range(limit + 1):
            if set(predecessors((x, y))) != set(brute_predecessors((x, y))):
                return False
    return True


def backward_tree(target: tuple[int, int], max_nodes: int = 100_000):
    """Candidate reverse tree; strict mass growth makes exact edges acyclic."""
    frontier = [target]
    seen = {target}
    parent_map = {}
    while frontier:
        next_frontier = []
        for state in frontier:
            parents = predecessors(state)
            parent_map[state] = parents
            for parent in parents:
                if parent not in seen:
                    seen.add(parent)
                    next_frontier.append(parent)
                    if len(seen) >= max_nodes:
                        return seen, parent_map, False
        frontier = next_frontier
    return seen, parent_map, True


def root_cone_exceptions(steps: int = 10_000):
    """Finite orbit scan from D(0,7); returns states outside new_affine_cone."""
    state = (0, 7)
    exceptions = []
    for i in range(steps):
        if not new_affine_cone(*state):
            exceptions.append((i, state))
        state = high_level_next(*state)
        if state is None:
            return exceptions, i + 1, True
    return exceptions, steps, False


def main() -> None:
    print("Source pin: google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b")
    print("Ray inverse vs brute force, targets 0..60:", check_small_grid(60))
    b7 = (486 * 7 + 42, 486 * 7 + 46)
    nodes, parents, closed = backward_tree(b7)
    print("B(7) candidate tree exhausted:", closed)
    print("B(7) candidate tree nodes:", len(nodes))
    print("Blank root in B(7) candidate tree:", (0, 7) in nodes)
    for state in sorted(nodes, key=lambda p: p[0] + p[1]):
        print(" ", state, "parents:", parents.get(state, []))
    exceptions, checked, halted = root_cone_exceptions(10_000)
    print("Root cone scan:", checked, "states; halted:", halted)
    print("Outside-cone states:", exceptions)


if __name__ == "__main__":
    main()
