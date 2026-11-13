#!/usr/bin/env python3
"""Exact Haar-survival bounds for the P1 inverse-shadow tree.

Only the standard library is used. The final generation is treated without a
depth cutoff: each parent cylinder contributes its exact child-existence set.
The cutoff T applies only to the first d-1 edges.
"""
from __future__ import annotations

from fractions import Fraction

from finite_cylinder_regression import children, root_children


CASES = (
    (8, 24, 4),
    (9, 24, 4),
    (8, 18, 5),
    (9, 18, 5),
    (8, 14, 6),
    (9, 14, 6),
    (8, 10, 7),
    (9, 10, 7),
)

EXPECTED = {
    (8, 24, 4): (15000, Fraction(493, 1024), Fraction(2019329, 4194304)),
    (9, 24, 4): (15625, Fraction(247, 512), Fraction(8093699, 16777216)),
    (8, 18, 5): (123462, Fraction(903, 2048), Fraction(115589, 262144)),
    (9, 18, 5): (130321, Fraction(57983, 131072), Fraction(57985, 131072)),
    (8, 14, 6): (708750, Fraction(12781, 32768), Fraction(12793, 32768)),
    (9, 14, 6): (759375, Fraction(26906311, 67108864),
                 Fraction(26926791, 67108864)),
    (8, 10, 7): (1610510, Fraction(23273201, 67108864),
                 Fraction(23731953, 67108864)),
    (9, 10, 7): (1771561, Fraction(3027538197, 8589934592),
                 Fraction(3077869845, 8589934592)),
}


def encode_cylinder(q0: int, level: int) -> int:
    """Injectively encode q == q0 (mod 2**level) as one integer."""
    assert 0 <= q0 < (1 << level)
    return (1 << level) | q0


def lower_survival_measure(side: int, cutoff: int, depth: int):
    """Exact union of full child-existence regions over bounded parent words."""
    assert side in (8, 9) and depth >= 2 and cutoff >= 2

    cylinders: set[int] = set()
    parent_count = 0

    def add_parent(node):
        nonlocal parent_count
        parent_count += 1
        q0, level, m, a, b = node
        assert b % 2 == 1

        if (side + m) % 2 == 0:
            # No child iff z=a+b*r == 2 (mod 4).
            bad = ((2 - a) * pow(b, -1, 4)) % 4
            for residue in range(4):
                if residue != bad:
                    cylinders.add(encode_cylinder(
                        q0 + (1 << level) * residue, level + 2))
        else:
            # No child iff z=a+b*r is odd.
            bad = ((1 - a) * pow(b, -1, 2)) % 2
            good = 1 - bad
            cylinders.add(encode_cylinder(
                q0 + (1 << level) * good, level + 1))

    def descend(node, remaining):
        if remaining == 1:
            add_parent(node)
            return
        for child in children(side, node, cutoff):
            descend(child, remaining - 1)

    for root in root_children(side, cutoff):
        descend(root, depth - 1)

    # Encodings sort first by level, then by residue. Thus every possible
    # ancestor is considered before its descendants.
    maximal: set[int] = set()
    for key in sorted(cylinders):
        level = key.bit_length() - 1
        q0 = key - (1 << level)
        covered = False
        for k in range(level):
            ancestor = (1 << k) | (q0 & ((1 << k) - 1))
            if ancestor in maximal:
                covered = True
                break
        if not covered:
            maximal.add(key)

    max_level = max(key.bit_length() - 1 for key in maximal)
    numerator = sum(
        1 << (max_level - (key.bit_length() - 1))
        for key in maximal
    )
    return Fraction(numerator, 1 << max_level), parent_count, len(cylinders), len(maximal)


def survival_bounds(side: int, cutoff: int, depth: int):
    lower, parent_count, candidates, maximal = lower_survival_measure(
        side, cutoff, depth)
    tail = Fraction(depth if side == 8 else depth - 1, 1 << cutoff)
    return lower, lower + tail, parent_count, candidates, maximal, tail


def main():
    for side, cutoff, depth in CASES:
        lower, upper, count, candidates, maximal, tail = survival_bounds(
            side, cutoff, depth)
        expected_count, expected_lower, expected_upper = EXPECTED[
            (side, cutoff, depth)]
        assert count == expected_count
        assert lower == expected_lower
        assert upper == expected_upper
        print(
            f"side={side} depth={depth} cutoff={cutoff} "
            f"parents={count} cylinders={candidates} maximal={maximal} "
            f"lower={lower} upper={upper} tail={tail}"
        )


if __name__ == "__main__":
    main()
