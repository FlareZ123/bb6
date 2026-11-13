#!/usr/bin/env python3
"""Exact dyadic-cylinder first/second moments for the P1 shadow feeders.

Uses only the standard library and the affine cylinder constructors in
finite_cylinder_regression.py.  All arithmetic in the census is integral or
Fraction-exact; floats are presentation only.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from fractions import Fraction
from math import factorial

from finite_cylinder_regression import children, root_children


def generation(side: int, cutoff: int, depth: int):
    nodes = root_children(side, cutoff)
    for _ in range(depth - 1):
        nodes = [
            child
            for node in nodes
            for child in children(side, node, cutoff)
        ]
    return nodes


def first_moment_formula(side: int, cutoff: int, depth: int) -> Fraction:
    if side == 8:
        root_mass = Fraction(2) - Fraction(1, 2 ** (cutoff - 1))
    elif side == 9:
        root_mass = Fraction(2) - Fraction(1, 2**cutoff)
    else:
        raise ValueError("side must be 8 or 9")
    generic_mass = Fraction(1) - Fraction(1, 2 ** (cutoff + 1))
    return root_mass * generic_mass ** (depth - 1)


def cylinder_statistics(nodes):
    """Return exact first/second moments and union measure.

    A cylinder is (q0,h), meaning q == q0 (mod 2**h).  Multiplicity is
    retained: different inverse words can define the same cylinder.
    """
    multiplicity = Counter((h, q0) for q0, h, *_ in nodes)

    mean = Fraction(0)
    second = Fraction(0)
    union = Fraction(0)
    maximal = []

    for (h, q0), weight in multiplicity.items():
        measure = Fraction(1, 2**h)
        mean += weight * measure

        # Every strict ancestor is another cylinder containing this one.
        ancestor_weight = sum(
            multiplicity.get((k, q0 % (2**k)), 0)
            for k in range(h)
        )
        second += (weight * weight + 2 * weight * ancestor_weight) * measure

        if ancestor_weight == 0:
            union += measure
            maximal.append((q0, h))

    maximal.sort(key=lambda item: (item[1], item[0]))
    return {
        "paths": len(nodes),
        "distinct_cylinders": len(multiplicity),
        "mean": mean,
        "second_moment": second,
        "union_measure": union,
        "maximal_cylinders": maximal,
    }


def second_moment_tail_bound(side: int, cutoff: int, depth: int) -> Fraction:
    """A rational upper bound for all omitted pair intersections.

    A length-d word has total cost M=sum(t_i+1), and cylinder level
    h=M-2 (side 8) or h=M-1 (side 9).  If any t_i>cutoff, then
    M >= cutoff+d+1.  For each K=max(M,N), there are at most
    2*binom(K-1,d-1)*binom(K,d) ordered pairs, each intersecting in
    measure at most 2**(c-K), where c=2 or 1.

    Bound binomial products by K**(2d-1)/((d-1)! d!) and sum the
    resulting geometric majorant using its first-term ratio bound.
    """
    c = 2 if side == 8 else 1
    if side not in (8, 9):
        raise ValueError("side must be 8 or 9")
    start = cutoff + depth + 1
    power = 2 * depth - 1
    ratio = Fraction((start + 1) ** power, 2 * start**power)
    if ratio >= 1:
        raise ValueError("cutoff too small for the stated ratio bound")
    leading = Fraction(
        2 ** (c + 1) * start**power,
        factorial(depth - 1) * factorial(depth) * 2**start,
    )
    return leading / (1 - ratio)


def serialise_fraction(value: Fraction):
    return {
        "exact": f"{value.numerator}/{value.denominator}",
        "decimal": float(value),
    }


def run_one(side: int, cutoff: int, depth: int, with_second: bool):
    nodes = generation(side, cutoff, depth)
    stats = cylinder_statistics(nodes)
    formula_mean = first_moment_formula(side, cutoff, depth)
    assert stats["mean"] == formula_mean, (
        side, cutoff, depth, stats["mean"], formula_mean
    )

    result = {
        "side": side,
        "cutoff": cutoff,
        "depth": depth,
        "paths": stats["paths"],
        "distinct_cylinders": stats["distinct_cylinders"],
        "mean": serialise_fraction(stats["mean"]),
        "union_lower_bound": serialise_fraction(stats["union_measure"]),
        "union_upper_bound": serialise_fraction(
            min(Fraction(1), stats["union_measure"] + 2 - stats["mean"])
        ),
        "maximal_cylinder_count": len(stats["maximal_cylinders"]),
    }
    if with_second:
        tail = second_moment_tail_bound(side, cutoff, depth)
        result["second_moment_cutoff"] = serialise_fraction(
            stats["second_moment"]
        )
        result["second_moment_tail_upper_bound"] = serialise_fraction(tail)
        result["second_moment_unrestricted_interval"] = {
            "lower": serialise_fraction(stats["second_moment"]),
            "upper": serialise_fraction(stats["second_moment"] + tail),
        }
    if depth <= 3:
        result["maximal_cylinders_q0_level"] = [
            [q0, h] for q0, h in stats["maximal_cylinders"]
        ]
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--exploratory",
        action="store_true",
        help="also compute higher-generation union lower/upper intervals",
    )
    args = parser.parse_args()

    reports = []
    # These cutoffs make the second-moment truncation error tiny while keeping
    # the exact cylinder enumeration modest.
    for side in (8, 9):
        reports.append(run_one(side, 64, 2, with_second=True))
        reports.append(run_one(side, 48, 3, with_second=True))

    if args.exploratory:
        for side in (8, 9):
            for cutoff, depth in ((16, 4), (12, 5), (8, 6)):
                reports.append(run_one(side, cutoff, depth, with_second=False))

    print(json.dumps(reports, indent=2))


if __name__ == "__main__":
    main()
