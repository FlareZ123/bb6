#!/usr/bin/env python3
"""Exact periodic certificates for twenty Sheep-Machine inverse exclusions.

This checks finite modular facts used by the mathematical proof in README.md.
Its assertions exhaust *all* j in the stated residue classes, not a bounded
numerical sample. No third-party dependencies.
"""
from math import gcd

RESIDUES = (15, 27, 87, 99, 123, 135, 159, 195, 207, 243, 267, 303, 315, 339, 375, 423, 447, 459, 483, 519)
# (denominator factor, exponent offset, numerator remainder function,
#  valid periods for a=0,1,..., expected admissible a values)
STAGES = (
    (5, 3, lambda a: 10 * a - 1,
     (4, 20, 12, 8, 20, 60, 28), frozenset({2})),
    (45, 6, lambda a: 107 + 90 * a,
     (36, 60, 108, 24, 180, 60, 252, 48, 324, 300),
     frozenset()),
)


def section_next(t):
    """Published Sheep return map, defined for positive integers."""
    assert t > 0
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    if u == 3:
        return t + a + 3
    return t + a + (u - 1) // 2


def inverse(y):
    """All predecessors t>=5 of y in the above map."""
    candidates = []
    for a in range((y // 3).bit_length()):
        power = 1 << a
        t_special = 3 * power
        if t_special >= 5 and t_special + a + 3 == y:
            candidates.append(t_special)
        modulus = 2 * power + 1
        numerator = 2 * y - 2 * a + 1
        if numerator > 0 and numerator % modulus == 0:
            u = numerator // modulus
            if u >= 5 and u % 2:
                t = power * u
                if 5 <= t < y:
                    candidates.append(t)
    return sorted(candidates)


def verify():
    for factor, offset, remainder, periods, expected in STAGES:
        for residue in RESIDUES:
            admissible = set()
            for a, period in enumerate(periods):
                modulus = factor * (2 ** (a + 1) + 1)
                assert pow(2, period, modulus) == 1, (factor, a, period)
                # Because each period works, the list is complete for
                # j=residue+540*k as k ranges over *all* natural numbers.
                cycle_length = period // gcd(period, 540)
                for k in range(cycle_length):
                    j = residue + 540 * k
                    if pow(2, j + offset, modulus) == remainder(a) % modulus:
                        admissible.add(a)
            assert admissible == expected, (factor, residue, admissible)
            print(f"factor={factor} residue={residue}: admissible a = {sorted(admissible)}")

    # Independent bounded sanity check for the inverse formula, explicitly
    # supplementary to (not part of) the all-exponent modular certificate.
    for y in range(5, 1000):
        predicted = inverse(y)
        actual = [t for t in range(5, y) if section_next(t) == y]
        assert predicted == actual, (y, predicted, actual)

    # Sanity check that all twenty residue classes fit the second-parent formula.
    for r in RESIDUES:
        for j in (r, r + 540, r + 1080):
            p = 1 << j
            y1 = (4 * p - 2) // 5
            y2 = (32 * p - 76) // 45
            assert section_next(y1) == p
            assert section_next(y2) == y1
            assert not inverse(y2), (j, inverse(y2))

    print("PASS: exact periodic certificate and bounded independent inverse tests")


if __name__ == "__main__":
    verify()
