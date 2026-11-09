"""Exact arithmetic overlap certificate for Sheep fourth and fifth hidden-block exclusions.

Without optional --f5: only standard-library period and CRT arithmetic.
With --f5: independently runs the repository's existing SymPy-based F-depth-five
inverse tree from agent16-sheep-new-even-cones/prior_f5_overlap.py.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from math import gcd
from pathlib import Path
import sys

OLD_E = (
    (138, 4860), (1218, 4860), (402, 4860), (1738, 4860),
    (118, 14580), (246, 24300), (558, 8100), (846, 8100),
    (702, 11340), (188, 55080), (190, 306180), (220, 55080),
    (262, 53460), (442, 1837080), (624, 29160), (648, 122472),
)


def incoming_conditions(level: int, m: int) -> tuple[bool, ...]:
    assert m % 3, "This theorem is restricted to v3(j)=3 or 4"
    shared = (m % 2 == 1, m % 4 == 2, m % 2 == 1)
    if level == 4:
        return shared + (m % 7 == 2, m % 9 == 8, m % 15 == 7)
    assert level == 5
    return shared + (m % 7 == 3, m % 2 == 1, m % 9 == 4, m % 15 == 11)


def no_parent(level: int, m: int) -> bool:
    if level == 4:
        return m % 3 != 0 and m % 4 == 0 and m % 7 != 2 and m % 9 != 8 and m % 15 != 7
    if level == 5:
        return m % 3 != 0 and m % 4 == 0 and m % 7 != 3 and m % 9 != 4 and m % 15 != 11
    raise ValueError(level)


def new_classes(level: int) -> list[int]:
    out = []
    histogram = Counter()
    for m in range(1260):
        if m % 3 == 0:
            continue
        degree = sum(incoming_conditions(level, m))
        histogram[degree] += 1
        assert no_parent(level, m) == (degree == 0)
        if degree == 0:
            out.append(m)
    expected = {4: {0: 132, 1: 202, 2: 342, 3: 148, 4: 16},
                5: {0: 132, 1: 202, 2: 78, 3: 272, 4: 140, 5: 16}}[level]
    assert histogram == expected, (level, histogram)
    assert len(out) == 132
    return out


def main() -> None:
    s4 = new_classes(4)
    s5 = new_classes(5)
    # CRT: A+tB and C+uD have an integer intersection iff gcd(B,D)|(A-C).
    for level, seeds, scale in ((4, s4, 54), (5, s5, 162)):
        period = scale * 1260
        for m in seeds:
            j = scale * m
            assert j % 216 == 0
            for prior_j, prior_period in OLD_E:
                assert (j - prior_j) % gcd(period, prior_period), (
                    'previous even-cone overlap', level, m, prior_j, prior_period
                )
        print(f'PASS h={level}: 132 exact predecessor-free m classes /1260, ' +
              f'density {Fraction(132,period)} of all exponent indices')
        print(f'PASS h={level}: no overlap with all {len(OLD_E)} prior E cone classes')

    gain = Fraction(len(s4), 54 * 1260) + Fraction(len(s5), 162 * 1260)
    assert gain == Fraction(22, 8505), gain
    assert all(m % 3 for m in s4 + s5)
    print('PASS exact disjoint union density:', gain, 'of all exponent indices')
    print('PASS simple new infinite families: j=216+68040*k, j=1296+204120*k')
    assert 4 in s4 and 8 in s5
    if '--f5' in sys.argv:
        folder = Path(__file__).resolve().parents[1] / 'agent16-sheep-new-even-cones'
        sys.path.insert(0, str(folder))
        from prior_f5_overlap import closes
        from hashlib import sha256
        old = {r for r in range(5400) if closes((0, 0, 1), r, 5)}
        assert len(old) == 3596
        digest = sha256(','.join(map(str, sorted(old))).encode()).hexdigest()
        assert digest == 'dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b'
        assert all(r not in old for r in range(0, 5400, 216))
        for level, seeds, scale in ((4, s4, 54), (5, s5, 162)):
            for m in seeds:
                step = scale * 1260
                period = 5400 // gcd(5400, step)
                assert all((scale * m + step * k) % 5400 not in old
                           for k in range(period))
        print('PASS existing 3596/5400 F-depth-five exclusions disjoint from all new classes')


if __name__ == '__main__':
    main()
