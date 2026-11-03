"""Bounded-reset, unbounded-depth exact source inverse census for P1 n=16q+2 feeders.

The parameter window is finite, but there is no arbitrary time/depth/queue cap:
all inverseAt branches and all histories with reset count <= max_resets
are exhausted. No universal no-halting conclusion is inferred.
"""

from collections import Counter, deque


def source_inverse_at(b: int, d: int):
    """Enumerate all (t,k,c) with source inverseAt b d t = some(k,c)."""
    if b < 4 or b % 4:
        return
    t, k, c = 0, b // 4 - 1, d + b // 2
    while True:
        yield t, k, c
        if c < 3 or c % 2 == 0:
            return
        v = (c - 3) // 2
        k, c, t = k + v // 2 + 1, v, t + 1


def census(q: int, root: int, max_resets: int = 2):
    """Exhaust the exact odd inverse cone with <= max_resets positive t edges."""
    assert q >= 1 and root in (0, 1) and max_resets >= 0
    p = 2 ** (16 * q)
    u = 7 * p - 4 * q - 3
    b0, d0, delta = (4 * u - 4, 4 * u + 9, 12) if root == 0 else (6 * u - 2, 2 * u + 5, 16)
    mass = b0 + d0
    queue = deque([(b0, d0, 0, 0)])
    seen = {(b0, d0, 0): 0}
    counts = Counter()
    closest = None
    nonpositive = 0
    while queue:
        b, d, m, z = queue.popleft()
        assert b + d + 2 * m == mass, (q, root, b, d, m, z)
        counts[z] += 1
        gap = b - (4 * m + 64 * q + delta)
        if gap <= 0:
            nonpositive += 1
        if closest is None or abs(gap) < abs(closest[0]):
            closest = (gap, m, z)
        if b < 8 or b % 4 or d % 2 == 0:
            continue
        for t, k, c in source_inverse_at(b, d):
            if k < 2 or c % 2 == 0:
                continue
            nz = z + int(t > 0)
            if nz > max_resets:
                continue
            b2, d2, m2 = 2 * k - 4, c + 4, m + t + 1
            assert b2 + d2 + 2 * m2 == mass
            key = (b2, d2, nz)
            if key in seen:
                assert seen[key] == m2, (q, root, key, seen[key], m2)
                continue
            seen[key] = m2
            queue.append((b2, d2, m2, nz))
    return len(seen), counts, closest, nonpositive


def main():
    total, gaps, counts = 0, Counter(), Counter()
    for q in range(1, 1001):
        for root in (0, 1):
            nodes, sectors, closest, nonpositive = census(q, root)
            total += nodes
            counts.update(sectors)
            gaps["all_positive" if nonpositive == 0 else "some_nonpositive"] += 1
            if nonpositive:
                print("COUNTEREXAMPLE TO CANDIDATE GLOBAL GAP:", q, root, nonpositive, closest)
        if q % 200 == 0:
            print("checked q <=", q, "total nodes", total, "resets-count census", dict(counts), flush=True)
    print("FINAL nodes", total, "positive/zero/negative closest gaps", dict(gaps), "reset-count totals", dict(counts))


if __name__ == "__main__":
    main()
