"""Finite 4096-cell certificate for Machine C's exact two-step image density.

Uses the source-derived full predecessor equations and the elementary one-step
image criterion from results/2026-11-08-machine-c-exact-two-step-image-density-agent34.md.
The independent original-source regression imports the sibling check_degree.py.
"""

from collections import Counter
from random import Random

from check_degree import inverse_candidates, degree_formula


def image_parent(a: int, b: int) -> bool:
    assert b >= 5
    return b % 2 == 0 or (a + b) % 4 in (0, 3)


def two_step_residue(s: int, y: int) -> bool:
    assert 0 <= s < 64 and 0 <= y < 64
    S = 256 + s
    Y = 64 + y
    X = S - Y
    Q = S + S % 2
    v = (Q & -Q).bit_length() - 1
    if v >= 5:
        return True
    if Y % 2 == 0 and image_parent(S - 2, (Y - 2) // 2):
        return True
    for n in range(v - 1):
        if S % 2 == 0:
            if (n + 1) % 2 != X % 2:
                continue
            a = Q // (1 << (n + 1)) - 2
        else:
            if n % 2 != X % 2:
                continue
            a = Q // (1 << (n + 1)) - 3
        numerator = S + Y - a - 7 - 3 * n
        assert numerator % 2 == 0 and a >= 2 and numerator > a
        k = numerator // 2
        assert k >= 5
        if image_parent(a, k):
            return True
    return False


def exact_depth_two(x: int, y: int) -> bool:
    return any(p[1] >= 5 and degree_formula(*p) > 0
               for p in inverse_candidates(x, y))


def test() -> None:
    truth = {(s, y): two_step_residue(s, y)
             for s in range(64) for y in range(64)}
    assert sum(truth.values()) == 2448

    bands: Counter[tuple[int, bool]] = Counter()
    for s in range(64):
        q = (256 + s) + ((256 + s) % 2)
        v = (q & -q).bit_length() - 1
        band = min(v, 5)
        for y in range(64):
            bands[band, truth[s, y]] += 1

    print("Residue count by min(v2(Q),5), hit/miss:")
    print(sorted(bands.items()))
    print("Exact eventual image density:", sum(truth.values()), "/4096 = 153/256")

    for x in range(8, 1024):
        for y in range(12, 1024):
            assert exact_depth_two(x, y) == truth[(x + y) % 64, y % 64], (x, y)
    print("PASS: 1,028,192 complete small-target source-shaped comparisons")

    rng = Random(663746)
    for _ in range(100_000):
        x = rng.randrange(8, 1 << rng.randint(10, 30))
        y = rng.randrange(12, 1 << rng.randint(10, 30))
        assert exact_depth_two(x, y) == truth[(x + y) % 64, y % 64], (x, y)
    print("PASS: 100,000 additional randomized large-target comparisons")


if __name__ == "__main__":
    test()
