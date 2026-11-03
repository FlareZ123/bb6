"""Independent exact-arithmetic BB6 Machine C even-zero predecessor audit.

Mirror of repository commit f5103ce fast-section/bounce definitions. The
weighted source mass bound is proven separately by section_mass_strict.
"""
from collections import defaultdict


def bounce(k: int, c: int):
    while True:
        if c < 4:
            return None
        if k % 2:
            if c <= 2 * k + 6:
                return 2 * k + 6 - c, c
            c -= 2 * k + 3
            k = 2 * k + 3
        else:
            if c == 4:
                return 2 * k + 2, 3
            if c == 5:
                return None
            if c <= 2 * k + 8:
                return 2 * k + 8 - c, c - 1
            c -= 2 * k + 5
            k = 2 * k + 4


def sec_next(a: int, k: int):
    if a == 0:
        if k == 0:
            return None
        if k == 1:
            return 0, 4
        return bounce(1, 2 * k + 1)
    if a == 1:
        if k == 0:
            return 5, 1
        if k == 1:
            return 2, 3
        if k == 2:
            return 2, 5
        if k == 3:
            return 0, 7
        return bounce(4, 2 * k - 3)
    if k == 0:
        return a - 2, 2
    if 2 * k <= a:
        return a - 2 * k, 2 * k + 2
    return bounce(a - 1, 2 * k - a + 3)


def predicted_parents(y: int):
    result = {(y - 2, y // 2 - 1)}
    power = 1
    r = 0
    while 8 * power <= y:
        if y % (8 * power) == 0:
            u = y // (8 * power)
            if u >= 2:
                result.add((2 * u - 2, y - (u + 4 + 3 * r)))
        if 16 * power == y:
            result.add((0, y - (3 * r + 6)))
        power *= 4
        r += 1
    return result


def audit(max_y: int = 512):
    parents = defaultdict(set)
    source_count = 0
    # Source-mass theorem: a+2k+2 <= x+2y = 2y.
    # All sources of targets y<=max_y are in this finite triangle.
    for a in range(2 * max_y - 1):
        for k in range((2 * max_y - a - 2) // 2 + 1):
            source_count += 1
            target = sec_next(a, k)
            if (target is not None and target[0] == 0
                    and 16 <= target[1] <= max_y and target[1] % 2 == 0):
                parents[target[1]].add((a, k))
    total_parents = 0
    for y in range(16, max_y + 1, 2):
        found = parents[y]
        predicted = predicted_parents(y)
        assert found == predicted, (y, sorted(found - predicted), sorted(predicted - found))
        total_parents += len(found)
    print('Source-prefix revision f5103cebbf6466c630c764d0311f4528f28bf686')
    print('Max target even zero-first y:', max_y)
    print('Exhaustive checked target values:', len(range(16, max_y + 1, 2)))
    print('Source triangle count:', source_count)
    print('Total (a,k)->(0,y) edges checked:', total_parents)
    print('Every even target y in [16,max] matched the 3-sector formula: YES')
    print('Examples:')
    for y in [16, 18, 24, 32, 64, 128, 252, 256, 512]:
        print(' y=', y, 'parents=', sorted(parents[y]))
    p = (5, 1)
    reached_252 = False
    for step in range(100):
        if p == (250, 125):
            print('Authentic section step', step, '=', p)
        if p == (0, 252):
            reached_252 = True
            print('Authentic section step', step, '=', p)
        p = sec_next(*p) if p is not None else None
    assert reached_252


if __name__ == '__main__':
    audit()
