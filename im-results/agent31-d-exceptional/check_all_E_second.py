"""Exact full two-return classification of the source-derived E exception.

The universal formulas are derived from pre-existing source-certified B, A-code,
E-triple and E-double macros. This script is a bounded independent raw check.
"""
from __future__ import annotations

from check_second_escape import one, pairs, physical_return
from check_root_L_escape import L, parse_bits


def triple_cost(m: int, count: int) -> int:
    return count * (6 * m + 41) + 12 * count * (count - 1)


def second_prediction(k: int, q: int) -> tuple[int, list[int]]:
    assert k >= 0 and q >= 1
    t, residue = divmod(k, 3)
    if q == 1:
        if residue == 0:
            K = 8 * t
            return 12 * K * K + 73 * K + 127, one(64 * t + 27)
        if residue == 1:
            K = 8 * t + 3
            return 12 * K * K + 49 * K + 40, one(64 * t + 37) + pairs(3)
        K = 8 * t + 5
        return 12 * K * K + 49 * K + 58, one(64 * t + 49) + pairs(6)
    if residue == 0:
        K = 8 * t + 1
        return 12 * K * K + 49 * K + 40, one(64 * t + 17 + 2 * q) + [0] + one(6)
    if residue == 1:
        K = 8 * t + 3
        final = one(64 * t + 33) + pairs(2) + [0] + one(2 * q - 3) + [0] + one(6)
        return 12 * K * K + 49 * K + 58, final
    K = 8 * t + 6
    m = 4 * K + 3
    r, s = divmod(2 * q, 3)
    prefix = 12 * K * K + 41 * K + 32
    code = triple_cost(m, r)
    if s == 0:
        return prefix + code + 2 * (m + 4 * r) + 6, one(8 * K + 17 + 8 * r)
    if s == 1:
        cost = (prefix + code + 2 + (6 * (m + 4 * r + 1) + 41)
                + (6 * (m + 4 * r + 5) + 41) + 2 * (m + 4 * r + 9) + 6)
        return cost, one(8 * K + 29 + 8 * r)
    return (prefix + code + 2 * (m + 4 * r) + 24,
            one(8 * K + 11 + 8 * r) + pairs(3) + one(2))


def first_prediction(k: int, q: int) -> tuple[int, list[int]]:
    if q == 1:
        return (12 * k * k + 49 * k + 96,
                one(8 * k + 3) + [0] + one(4) + [0] + [1, 0] * 3)
    return (12 * k * k + 49 * k + 56 + 4 * q,
            one(8 * k + 5) + [0] + one(2 * q) + [0] + one(6))


def main() -> None:
    cases = 0
    outside = 0
    for k in range(12):
        for q in range(1, 13):
            start = one(3 * k + 4) + pairs(q) + [1]
            t1, w1 = physical_return(start)
            t2, w2 = physical_return(w1)
            p1, v1 = first_prediction(k, q)
            p2, v2 = second_prediction(k, q)
            while v1 and v1[-1] == 0:
                v1.pop()
            assert (t1, w1) == (p1, v1), ('first', k, q, t1, p1)
            if v2 and v2[-1] == 0:
                v2 = v2[:-1]
            assert (t2, w2) == (p2, v2), ('second', k, q, t2, p2)
            expected_outside = k % 3 == 1 and q >= 3
            assert (parse_bits(w2.copy()) is None) == expected_outside, (k, q)
            outside += expected_outside
            cases += 1
    print(f'PASS {cases}/{cases} full physical two-return time+tape predictions; '
          f'{outside} outside regular L (exactly k mod 3=1 and q>=3)')


if __name__ == '__main__':
    main()
