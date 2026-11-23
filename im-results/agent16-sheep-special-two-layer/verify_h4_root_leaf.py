#!/usr/bin/env python3
"""Exact arithmetic audit for H4-ODD-ROOT-LEAF.md (stdlib only)."""
from fractions import Fraction
from math import gcd, lcm
import json


def v3(n: int) -> int:
    if n == 0:
        return 10**9
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def exact_roots(s: int) -> list[int]:
    modulus = 3 ** (s + 8)
    roots = []
    for r in range(3 ** (s + 1)):
        n = (pow(2, 1211 + 1458 * r, modulus) - 4055) % modulus
        if v3(n) == s + 7:
            roots.append(r)
    return roots


EXPECTED_ROOTS = {
    0: [0, 1],
    1: [2, 5],
    2: [8, 17],
    3: [26, 53],
    4: [161, 242],
    5: [80, 323],
    6: [1295, 2024],
    7: [2753, 4940],
    8: [566, 13688],
}


def generic_parent_hits(s: int, c: int, roots: list[int]) -> tuple[int, int, list[int]]:
    q = 2 ** (c + 1) + 1
    modulus = 3 ** (s + 7) * q
    t = v3(q)
    p2 = 2 * (c + 1) // gcd(2 * (c + 1), 1458)
    p = lcm(3 ** (s + t), p2)
    period = lcm(2 * 3 ** (s + 1), p)
    step = pow(2, 1458, modulus)
    assert pow(step, p, modulus) == 1
    k = 2 ** (s + 1) * 4055 + 3 ** (s + 7) * (2 * c - 3)
    value = pow(2, 1212 + s, modulus)
    hits = []
    for r in range(period):
        eligible = (r % 2 == 1 and r % (3 ** (s + 1)) in roots)
        if eligible and value == k % modulus:
            hits.append(r)
        value = value * step % modulus
    return p, period, hits


EXPECTED_HITS = {
    0: {2: (18, [3]), 4: (30, [25])},
    1: {2: (54, [5])},
    2: {2: (162, [89])},
    3: {2: (486, [215]), 3: (324, [107, 215]), 4: (810, [269])},
    4: {2: (1458, [1133])},
    5: {2: (4374, [323])},
    6: {2: (13122, [10043])},
    7: {2: (39366, [11501]), 3: (26244, [2753, 11501]), 4: (65610, [2753])},
    8: {2: (118098, [33371]), 4: (196830, [98981])},
}


def h4_parent_table() -> tuple[list[int], dict[int, list[int]]]:
    periods = []
    hits_by_b = {}
    for b in range(1, 13):
        q = 2 ** (b + 1) + 1
        modulus = 243 * q
        step = pow(2, 162, modulus)
        p = 1
        value = step
        while value != 1:
            value = value * step % modulus
            p += 1
        combined_period = lcm(p, 3)  # exact h=4 requires k != 2 mod 3
        target = (243 * (2 * b - 3)) % modulus
        value = pow(2, 70, modulus)
        hits = []
        for k in range(combined_period):
            if k % 3 != 2 and (32 * (value - 7)) % modulus == target:
                hits.append(k)
            value = value * step % modulus
        periods.append(p)
        if hits:
            hits_by_b[b] = hits
    return periods, hits_by_b


FAMILY = [
    (0, 30, [1, 7, 13, 19]),
    (0, 18, [9, 15]),
    (1, 18, [11]),
    (1, 54, [23, 41]),
    (2, 54, [17]),
    (2, 162, [35, 143]),
    (3, 4860, [53, 377, 593, 917, 1025, 1241, 1349, 1565, 1997,
               2213, 2321, 2537, 2861, 2969, 3185, 3293, 3833, 3941,
               4157, 4265, 4481, 4805]),
    (4, 486, [485]),
    (4, 1458, [161, 647]),
    (5, 1458, [809]),
    (5, 4374, [1781, 3239]),
    (6, 4374, [4211]),
    (6, 13122, [1295, 5669]),
    (7, 393660, [15875, 24623, 42119, 77111, 94607, 103355, 120851, 147095,
                155843, 173339, 182087, 225827, 234575, 252071, 260819, 278315,
                304559, 313307, 339551, 357047, 383291, 392039]),
    (8, 590490, [20249, 59615, 72737, 112103, 138347, 177713, 190835, 217079,
                 230201, 256445, 308933, 335177, 348299, 374543, 413909, 427031,
                 453275, 466397, 532007, 545129, 571373, 584495]),
]

OLD_SETS = [
    (72, [17, 23, 35, 41, 59, 71]),  # A5
    (120, [9, 15, 27, 39, 51, 57, 75, 81, 87, 99, 105, 111]),  # A3
    (20, [0, 12, 16]),  # A0
    (216, [7, 19, 43, 55, 79, 115, 127, 151, 163, 187]),  # A1
    (648, [31, 139, 211, 247, 319, 355, 463, 535, 571, 643]),  # A2
    (1944, [175, 283, 499, 607, 823, 1147, 1255, 1471, 1579, 1795]),  # A3'
]


def check_family(roots_by_s: dict[int, list[int]], hits_by_s: dict[int, list[tuple[int, list[int]]]]) -> None:
    for s, modulus, residues in FAMILY:
        for r0 in residues:
            assert r0 % 2 == 1
            assert r0 % (3 ** (s + 1)) in roots_by_s[s]

    # Distinct progressions in the displayed union do not intersect.
    for i, (s1, m1, rs1) in enumerate(FAMILY):
        for s2, m2, rs2 in FAMILY[i + 1:]:
            g = gcd(m1, m2)
            for r1 in rs1:
                for r2 in rs2:
                    assert (r1 - r2) % g != 0, (s1, m1, r1, s2, m2, r2)

    # No selected progression intersects any finite generic-parent hit.
    for s, modulus, residues in FAMILY:
        for hit_period, hit_residues in hits_by_s[s]:
            g = gcd(modulus, hit_period)
            for r0 in residues:
                for hit in hit_residues:
                    assert (r0 - hit) % g != 0, (s, modulus, r0, hit_period, hit)

    # CRT-disjointness from the previous six progressions and the a == 2 mod 4 family.
    for s, modulus, residues in FAMILY:
        for r0 in residues:
            assert (1201 + 1458 * r0) % 4 == 3
            for old_modulus, old_residues in OLD_SETS:
                g0 = gcd(1458, old_modulus)
                period = old_modulus // g0
                inverse = pow(1458 // g0, -1, period)
                joint_gcd = gcd(modulus, period)
                for target in old_residues:
                    rhs = target - 1201
                    if rhs % g0:
                        continue
                    target_r = ((rhs // g0) * inverse) % period
                    assert (r0 - target_r) % joint_gcd != 0, (s, r0, old_modulus, target)


def check_special_source_intervals() -> dict[int, str]:
    a_min = 2659
    intervals = {
        0: (Fraction(3, 8), Fraction(1, 2)),
        1: (Fraction(1, 4), Fraction(3, 8)),
        2: (Fraction(3, 16), Fraction(1, 4)),
        3: (Fraction(1, 8), Fraction(3, 16)),
        4: (Fraction(1, 16), Fraction(3, 32)),
        5: (Fraction(3, 64), Fraction(1, 16)),
        6: (Fraction(1, 32), Fraction(3, 64)),
        7: (Fraction(3, 128), Fraction(1, 32)),
        8: (Fraction(1, 64), Fraction(3, 128)),
    }
    ratios = {}
    for s, (lower, upper) in intervals.items():
        if s == 0:
            ratio = Fraction(1024, 2187) - Fraction(1868, 2187 * 2 ** a_min)
            limit = Fraction(1024, 2187)
            correction_coefficient = Fraction(-1868, 2187)
        else:
            limit = Fraction(2 ** (s + 10), 3 ** (s + 7))
            correction_coefficient = Fraction(3 ** (s + 7) - 2 ** s * 4055, 3 ** (s + 7))
            ratio = limit + correction_coefficient / (2 ** a_min)
        assert abs(correction_coefficient) < 1
        assert Fraction(1, 2 ** a_min) < Fraction(1, 10000)
        assert lower < limit < upper
        assert lower < ratio < upper
        ratios[s] = str(ratio)

    # The s=0 candidate c=a-3 is strictly below x_a.
    assert 295 * 2 ** (a_min - 3) - 2187 * a_min - 1868 > 0

    # For s=2,5 the only candidates c=a-4,a-6 are odd, but 2^s | c+2 forces c even.
    assert (a_min - 4) % 2 == 1
    assert (a_min - 6) % 2 == 1

    # For s=7, c=a-7 and 2^7 | c+2 iff r == 58 (mod 64), an even class.
    parity_solutions = [r for r in range(64) if (1196 + 1458 * r) % 128 == 0]
    assert parity_solutions == [58] and parity_solutions[0] % 2 == 0

    # Exceptional cofactor-three source for X_a is trapped strictly between d=a-3 and d=a-2.
    g = lambda d: 729 * 2 ** d + 243 * d + 598
    assert g(a_min - 3) < 2 ** (a_min + 7) < g(a_min - 2)
    return ratios

def main() -> None:
    roots_by_s = {s: exact_roots(s) for s in range(9)}
    assert roots_by_s == EXPECTED_ROOTS, roots_by_s

    hits_by_s = {}
    hit_report = {}
    for s in range(9):
        hits = []
        for c in range(1, 2 * s + 17):
            _, period, residues = generic_parent_hits(s, c, roots_by_s[s])
            if residues:
                hits.append((c, period, residues))
        expected = EXPECTED_HITS[s]
        observed = {c: (period, residues) for c, period, residues in hits}
        assert observed == expected, (s, observed, expected)
        hits_by_s[s] = [(period, residues) for _, period, residues in hits]
        hit_report[s] = [
            {"c": c, "period": period, "r": residues}
            for c, period, residues in hits
        ]

    h4_periods, h4_hits = h4_parent_table()
    assert h4_periods == [2, 9, 4, 15, 2, 21, 8, 27, 10, 33, 4, 39]
    assert h4_hits == {2: [7]}, h4_hits

    assert v3(2 ** 1204 - 7) == 5
    assert v3(2 ** 1458 - 1) == 7

    # Check the uniform generic-parent cutoff at its base and increment.
    for s in range(9):
        c0 = 2 * s + 17
        k0 = 2 ** (s + 1) * 4055 + 3 ** (s + 7) * (2 * c0 - 3)
        assert 1 < k0 < 2 ** c0
        assert 2 * 3 ** (s + 7) < 2 ** c0

    ratios = check_special_source_intervals()
    check_family(roots_by_s, hits_by_s)

    r_density = sum((Fraction(len(rs), modulus) for _, modulus, rs in FAMILY), Fraction(0))
    assert r_density == Fraction(44579, 118098), r_density
    a_density = r_density / 1458
    assert a_density == Fraction(44579, 172186884), a_density
    combined = Fraction(158, 243) + a_density
    assert combined == Fraction(112001483, 172186884), combined

    print(json.dumps({
        "h4_parent_periods": h4_periods,
        "h4_parent_hits": h4_hits,
        "exact_valuation_root_classes": roots_by_s,
        "generic_parent_hits": hit_report,
        "special_source_interval_ratios_at_a_2659": ratios,
        "r_density": str(r_density),
        "a_density": str(a_density),
        "combined_with_prior_158_over_243": str(combined),
        "combined_percent": float(combined * 100),
        "s3_safe_residue_count_mod_4860": 22,
        "s7_safe_residue_count_mod_393660": 22,
        "s8_safe_residue_count_mod_590490": 22,
        "disjoint_from_prior_progressions": True,
    }, indent=2))


if __name__ == "__main__":
    main()
