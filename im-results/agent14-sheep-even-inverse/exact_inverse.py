"""Exact inverse of the source-certified Sheep even-return accelerator.

All arithmetic uses unbounded Python integers. No files are written.
The independently published return map, and its source-level semantics,
are in im-results/agent16-sheep-even-return/.
"""
from functools import lru_cache
from hashlib import sha256


def section_next(t):
    if t < 3:
        return None
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    return t + a + (3 if u == 3 else (u - 1) // 2)


def even_next(t):
    z = section_next(t)
    if z is None:
        return None
    p = z - 1
    h = (p & -p).bit_length() - 1
    return 1 + pow(3, h) * (p >> h)


@lru_cache(maxsize=200000)
def even_parents(y):
    """All even sources t>=6 satisfying E(t)=y, exhaustively."""
    if y % 2 or y < 6:
        return ()
    v = y - 1
    h = 0
    p3 = 1
    parents = set()
    while v % p3 == 0:
        z = 1 + (1 << h) * (v // p3)
        for a in range(1, z.bit_length()):
            den = (1 << (a + 1)) + 1
            numer = 2 * z - 2 * a + 1
            if numer <= 0:
                break
            u, remainder = divmod(numer, den)
            if remainder == 0 and u >= 5 and u % 2:
                parents.add((1 << a) * u)
            if 3 * (1 << a) + a + 3 == z:
                parents.add(3 * (1 << a))
        h += 1
        p3 *= 3
    return tuple(sorted(parents))


@lru_cache(maxsize=200000)
def direct_parents(y):
    """All section-map predecessors (odd and even), for the baseline."""
    if y < 6:
        return ()
    parents = set()
    for a in range(y.bit_length()):
        den = (1 << (a + 1)) + 1
        numer = 2 * y - 2 * a + 1
        if numer <= 0:
            break
        u, remainder = divmod(numer, den)
        if remainder == 0 and u >= 5 and u % 2:
            parents.add((1 << a) * u)
        if a >= 1 and 3 * (1 << a) + a + 3 == y:
            parents.add(3 * (1 << a))
    return tuple(sorted(parents))


def first_closed_depth(y, parents, initial, max_depth=5):
    frontier = {y}
    for depth in range(1, max_depth + 1):
        if initial in frontier:
            return 0
        frontier = {x for z in frontier for x in parents(z)}
        if not frontier:
            return depth
    return 0


def verify():
    # Forward E is a block of ordinary F transitions to the first even state.
    for t in range(6, 2000, 2):
        y = even_next(t)
        if y is None:
            continue
        z = section_next(t)
        while z % 2:
            z = section_next(z)
        assert z == y and y > t
        assert t in even_parents(y)

    # An independent, literal exhaustive inverse check on small target values.
    for y in range(6, 1202, 2):
        brute = tuple(t for t in range(6, y, 2) if even_next(t) == y)
        assert even_parents(y) == brute, (y, even_parents(y), brute)

    ordinary = []
    accelerated = []
    counts = {d: 0 for d in range(1, 6)}
    for j in range(100, 1100):
        target = 1 << j
        d = first_closed_depth(target, even_parents, 10)
        if d:
            accelerated.append(j)
            counts[d] += 1
        if first_closed_depth(target, direct_parents, 5):
            ordinary.append(j)
    extra = sorted(set(accelerated) - set(ordinary))
    assert counts == {1: 351, 2: 248, 3: 179, 4: 84, 5: 49}
    assert len(ordinary) == 802 and len(accelerated) == 911
    assert len(extra) == 109
    assert set(ordinary) <= set(accelerated)
    digest = lambda xs: sha256(",".join(map(str, xs)).encode()).hexdigest()
    assert digest(accelerated) == "bd8b51ce28577ea2e8b02aaaf2bf71f5cc17faf036c91e654f5b3e0abbf4b7ab"
    assert digest(extra) == "1408bd348ad38583499097b6e556f17d0e8e0575d1c489d246fd487217eaf2d5"
    print("PASS: 999 forward checks; 598 brute-force inverse tests")
    print("Exact E inverse 100..1099: 911/1000 closed within depth 5")
    print("First closure by E depth:", counts)
    print("Unaccelerated F inverse: 802/1000 closed within depth 5")
    print("Additional E-closed targets at depth 5:", len(extra))
    print("E-closed index SHA256:", digest(accelerated))
    print("Additional-index SHA256:", digest(extra))


if __name__ == "__main__":
    verify()
