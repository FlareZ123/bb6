"""Independent source-shaped regression for Machine C's exact indegree profile.

Original Lean semantics: im-results/agent46-c-jump/FastSectionDef.lean.
Full source predecessor iff: SectionAllInverse.lean.
This script supplies finite evidence; the all-target argument is in results/.
"""

from random import Random


def bounce(k: int, c: int) -> tuple[int, int] | None:
    while c >= 4:
        if k % 2:
            if c <= 2 * k + 6:
                return 2 * k + 6 - c, c
            c, k = c - (2 * k + 3), 2 * k + 3
        else:
            if c == 4:
                return 2 * k + 2, 3
            if c == 5:
                return None
            if c <= 2 * k + 8:
                return 2 * k + 8 - c, c - 1
            c, k = c - (2 * k + 5), 2 * k + 4
    return None


def sec_next(a: int, k: int) -> tuple[int, int] | None:
    if a == 0:
        return None if k == 0 else ((0, 4) if k == 1 else bounce(1, 2 * k + 1))
    if a == 1:
        return ((5, 1), (2, 3), (2, 5), (0, 7))[k] if k <= 3 else bounce(4, 2 * k - 3)
    if k == 0:
        return a - 2, 2
    if 2 * k <= a:
        return a - 2 * k, 2 * k + 2
    return bounce(a - 1, 2 * k - a + 3)


def v2(q: int) -> int:
    return (q & -q).bit_length() - 1


def inverse_candidates(x: int, y: int) -> set[tuple[int, int]]:
    """Derive algebraic candidates from full inverse equations; check source edges."""
    assert x >= 0 and y >= 5
    s = x + y
    q = s + s % 2
    v = v2(q)
    z = x + 2 * y
    parents: set[tuple[int, int]] = set()

    if y % 2 == 0:
        parents.add((s - 2, (y - 2) // 2))
    if (x, y) == (2, 5):
        parents.add((1, 2))
    if (x, y) == (0, 7):
        parents.add((1, 3))

    if s % 2 == 0:
        if q == 1 << v and v >= 3:
            n = v - 3
            cost = z - 9 - 3 * n
            if cost >= 4 and cost % 2 == 0:
                parents.add((0, cost // 2))
        for n in range(v - 1):
            if (n + 1) % 2 != x % 2:
                continue
            a = q // (1 << (n + 1)) - 2
            cost = z - a - 7 - 3 * n
            if a >= 2 and cost > a and cost % 2 == 0:
                parents.add((a, cost // 2))
    else:
        if q == 1 << v and v >= 4:
            n = v - 4
            cost = z - 11 - 3 * n
            if cost >= 8 and cost % 2 == 0:
                parents.add((1, cost // 2))
        for n in range(v - 1):
            if n % 2 != x % 2:
                continue
            a = q // (1 << (n + 1)) - 3
            cost = z - a - 7 - 3 * n
            if a >= 3 and cost > a and cost % 2 == 0:
                parents.add((a, cost // 2))

    return {p for p in parents if sec_next(*p) == (x, y)}


def degree_formula(x: int, y: int) -> int:
    assert x >= 0 and y >= 5
    s = x + y
    q = s + s % 2
    v = v2(q)
    base = v // 2 + int(v % 2 == 1 and y % 2 == 0)
    if q != 1 << v:
        return base
    if s % 2 == 0:
        return base + (1 if x % 2 == v % 2 else -1)
    return base - int(x % 2 == v % 2)


def test() -> None:
    rng = Random(746623)
    targets = [(x, y) for x in range(220) for y in range(5, 220)]
    for _ in range(50_000):
        s = rng.randint(6, 1 << rng.randint(4, 25))
        y = rng.randint(5, s)
        targets.append((s - y, y))

    for x, y in targets:
        degree = len(inverse_candidates(x, y))
        formula = degree_formula(x, y)
        assert degree == formula, (x, y, degree, formula)

    # Independently scan source pairs and verify that no source edge is
    # absent from the algebraic inverse candidate procedure.
    forward_count = 0
    for a in range(200):
        for k in range(200):
            out = sec_next(a, k)
            if out is None or out[1] < 5:
                continue
            assert (a, k) in inverse_candidates(*out), (a, k, out)
            forward_count += 1

    print(f"PASS: {len(targets):,} degree comparisons, "
          f"{forward_count:,} independently scanned source edges")
    for q in (8, 16, 32, 64, 128, 256):
        print(f"power-of-two diagonal Q={q}: "
              f"{[(x, q-x, degree_formula(x, q-x)) for x in range(q-5)] if q <= 16 else 'sampled by grid'}")


if __name__ == "__main__":
    test()
