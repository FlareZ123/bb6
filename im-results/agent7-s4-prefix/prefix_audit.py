"""Finite, independent replay of the source-mirrored S4 reduced map."""
from random import Random


def bump(xs, n):
    return xs[:] if n == 0 else ([xs[0] + n, *xs[1:]] if xs else [n - 1])


def epoch(a, left, right):
    left, right = left[:], right[:]
    while True:
        half = a // 2
        r = bump(right, half)
        if not left:
            if a <= 1:
                return None
            if a % 2:
                a, right = half, [0, *r]
                continue
            a, left, right = half - 1, [], bump(r, 2)
        else:
            b, tail = left[0], left[1:]
            if a % 2:
                a, left, right = b + half + 1, tail, [0, *r]
                continue
            a, left, right = b + half, tail, bump(r, 2)
        for digit in right:
            a, left = digit, [a, *left]
        return a, left


def reduced(xs):
    result = epoch(27, bump(xs, 31), [0, 6, 5, 3, 1])
    return None if result is None else bump(result[1][4:], 17)


def weight(xs):
    return sum((x + 1) << i for i, x in enumerate(xs))


fixed = [5, 7, 7, 19]
rng = Random(20261103)
for i in range(300):
    xs = [rng.randrange(120) for _ in range(i % 10)]
    full = (3, fixed + xs)
    for _ in range(32):
        if full is not None:
            full = epoch(full[0], full[1], [0])
    short = reduced(xs)
    assert full == (None if short is None else (3, fixed + short))

xs = [42, 12, 8, 5]
for i in range(27921):
    if i in (3, 40, 328, 3344, 27920):
        k = len(xs)
        total = 45 + weight(xs)
        assert total % (1 << k) == 0
        q = total >> k
        r = q.bit_length()
        z = (1 << r) - q - 1
        assert 45 + weight(xs + [z]) == (1 << (k + r))
        assert reduced(xs + [z]) is None
        print(i, k, q, z, k + r)
    xs = reduced(xs)
    assert xs is not None
print("PASS: 300 arbitrary 32-step comparisons; 27921 reduced-seed states")
