#!/usr/bin/env python3
"""Exact-integer exploration of the BB429 branch-29 signed Block tree.

This is an executable experiment, not a proof.  The formulas below transcribe
Signed429.allowed, Signed429.bad, and Signed429.Block from SignedDrift.lean.
Python's % on negative integers agrees with Lean Int.mod for positive moduli.
"""

from __future__ import annotations

import argparse


def allowed(a: int, b: int) -> bool:
    return (
        (a % 8 == 0 and b % 4 in (0, 2))
        or (a % 8 == 1 and b % 4 in (0, 1, 2))
        or (a % 8 == 2 and b % 4 == 2)
        or (a % 8 == 3 and b % 4 in (1, 2, 3))
        or (a % 8 == 4 and b % 4 == 2)
        or a % 8 == 5
        or (a % 8 == 6 and b % 4 == 2)
        or (a % 8 == 7 and b % 4 in (2, 3))
    )


def bad(u: int, d: int) -> bool:
    a = -u - 3
    b = 6 - 4 * u - d
    return (
        not allowed(a, b)
        or (a % 2 == 0 and b % 8 != 2)
        or (a % 8 == 7 and b % 8 == 7)
        or (a % 16 in (1, 5) and b % 8 == 6)
        or (a % 32 == 5 and b % 16 == 1)
    )


def candidate_children(u: int, d: int) -> list[tuple[str, int, int]]:
    """All algebraically guarded F/EF/SF children, including Bad endpoints."""
    out = []
    if u % 2 == 0:
        out.append(("F", u // 2, d + 3 * u + 3))
    if u % 2 == 1 and d % 8 == 0:
        out.append(("EF", u + (d + 8) // 8, d // 4 + 4))
    if u % 2 == 0 and d % 8 == 4:
        out.append(("SF", u + (d + 20) // 8, d // 4 - 1))
    return out


def valid_children(u: int, d: int) -> list[tuple[str, int, int]]:
    return [
        child for child in candidate_children(u, d)
        if not bad(child[1], child[2])
    ]


def tree_stats(t: int) -> tuple[int, int, int, int, int, int]:
    """Return height, unfolded nodes, leaf paths, unique states, Bad leaves, no-guard leaves."""
    start = (48 * t, 96 * t + 18)
    memo: dict[tuple[int, int], tuple[int, int, int]] = {}
    active: set[tuple[int, int]] = set()

    def visit(state: tuple[int, int]) -> tuple[int, int, int]:
        if state in memo:
            return memo[state]
        if state in active:
            raise RuntimeError(f"cycle detected for t={t} at {state}")
        active.add(state)
        u, d = state
        candidates = candidate_children(u, d)
        children = [
            (v, e) for _, v, e in candidates if not bad(v, e)
        ]
        for v, e in children:
            if not (v > 0 and e >= 2 and e != 4):
                raise AssertionError(f"Safe invariant failed: {(u,d)} -> {(v,e)}")
        if not children:
            result = (0, 1, 1)
        else:
            sub = [visit(child) for child in children]
            result = (
                1 + max(x[0] for x in sub),
                1 + sum(x[1] for x in sub),
                sum(x[2] for x in sub),
            )
        active.remove(state)
        memo[state] = result
        return result

    height, unfolded_nodes, leaf_paths = visit(start)
    bad_leaf_states = 0
    no_guard_leaf_states = 0
    for u, d in memo:
        if not valid_children(u, d):
            if candidate_children(u, d):
                bad_leaf_states += 1
            else:
                no_guard_leaf_states += 1
    return (
        height, unfolded_nodes, leaf_paths, len(memo),
        bad_leaf_states, no_guard_leaf_states,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--max-t", type=int, default=1 << 20,
        help="scan feeder parameters t=1,...,max_t (default: 2^20)",
    )
    args = parser.parse_args()
    if args.max_t < 1:
        raise SystemExit("--max-t must be positive")

    max_depth = (-1, None, None, None)
    max_nodes = (-1, None, None)
    max_leaves = (-1, None, None)
    max_margin = (-10**9, None, None)
    depth_bound_violations = 0
    total_bad_leaf_states = 0
    total_no_guard_leaf_states = 0
    prefix_rows = []

    for t in range(1, args.max_t + 1):
        height, nodes, leaves, unique, bad_leaves, no_guard = tree_stats(t)
        k = t - 1
        if height > max_depth[0]:
            max_depth = (height, k, nodes, leaves)
        if nodes > max_nodes[0]:
            max_nodes = (nodes, k, leaves)
        if leaves > max_leaves[0]:
            max_leaves = (leaves, k, nodes)
        margin = height - (2 * t.bit_length() + 1)
        if margin > max_margin[0]:
            max_margin = (margin, k, height)
        if margin > 0:
            depth_bound_violations += 1
        total_bad_leaf_states += bad_leaves
        total_no_guard_leaf_states += no_guard

        if t & (t - 1) == 0:
            n = t.bit_length() - 1
            prefix_rows.append((n, max_depth[0], max_depth[1]))

    print(f"scanned t=1..{args.max_t} (k=t-1)")
    print(f"max height: {max_depth}")
    print(f"max unfolded nodes: {max_nodes}")
    print(f"max leaf paths: {max_leaves}")
    print(f"max margin height-(2*bit_length(t)+1): {max_margin}")
    print(f"violations of empirical depth bound: {depth_bound_violations}")
    print(f"terminal unique states blocked by Bad: {total_bad_leaf_states}")
    print(f"terminal unique states with no algebraic guard: {total_no_guard_leaf_states}")
    print("prefix maxima for k=0,...,2^n-1:")
    for row in prefix_rows:
        print("  n=%2d  max_height=%2d  argmax_k=%d" % row)


if __name__ == "__main__":
    main()
