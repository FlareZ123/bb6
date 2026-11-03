"""Reproducible mixed96 / M32 necessary-stopping-target overlap audit.

Finite graph evidence only. The original-source Lean proof of the B8/M32
closed reachable set was checked in GitHub Actions run 41538277695.
The four additional mixed96 exclusions were separately Lean-proved by Agent4.
"""
from collections import deque


def step(a: int, k: int, c: int):
    if c == 1:
        return a, k + 1, 0
    if c == 2:
        return None
    if c == 3:
        return a, k + 2, 1
    if c == 0:
        if a == 0:
            return 1, 0, 2 * k + 2
        if a == 1:
            return (5, 0, 1) if k == 0 else (2, 2, 2 * k - 1)
        return a - 2, 1, 2 * k + 1
    if a == 0:
        return (2 * k + 2, 2, c - 3) if k % 2 == 0 else (2 * k + 3, 0, c)
    return a - 1, k + 1, c - 1


def quotient_closure(side, project, reps):
    def index(t):
        a, k, c = t
        return (a * side + k) * side + c

    seen = bytearray(side**3)
    seed = index(project((5, 0, 1)))
    seen[seed] = 1
    queue = deque([seed])
    count = edges = 0
    while queue:
        u = queue.popleft()
        count += 1
        a, k, c = u // (side * side), u // side % side, u % side
        for aa in reps(a):
            for kk in reps(k):
                for cc in reps(c):
                    t = step(aa, kk, cc)
                    if t is None:
                        continue
                    edges += 1
                    v = index(project(t))
                    if not seen[v]:
                        seen[v] = 1
                        queue.append(v)
    return seen, index, count, edges


def compare():
    mixed = lambda t: (t[0] % 96, t[1] % 96,
                       t[2] if t[2] < 2 else 2 + (t[2] - 2) % 48)

    def mixed_closure():
        def index(t):
            a, k, c = t
            return (a * 96 + k) * 50 + c

        seen = bytearray(96 * 96 * 50)
        origin = index((5, 0, 1))
        seen[origin] = 1
        queue = deque([origin])
        count = edges = 0
        while queue:
            u = queue.popleft()
            count += 1
            a, k, c = u // 4800, u // 50 % 96, u % 50
            for aa in (a, a + 96):
                for kk in (k, k + 96):
                    for cc in ((c,) if c < 2 else (c, c + 48)):
                        t = step(aa, kk, cc)
                        if t is None:
                            continue
                        edges += 1
                        v = index(mixed(t))
                        if not seen[v]:
                            seen[v] = 1
                            queue.append(v)
        return seen, index, count, edges

    mixed_seen, mixed_index, mixed_count, mixed_edges = mixed_closure()
    assert (mixed_count, mixed_edges) == (260672, 2022544)

    base, mod = 8, 32
    side = base + mod
    q = lambda x: x if x < base else base + (x - base) % mod
    q32 = lambda t: tuple(map(q, t))
    reps = lambda x: (x,) if x < base else (x, x + mod)
    m32_seen, m32_index, m32_count, m32_edges = quotient_closure(
        side, q32, reps)
    assert (m32_count, m32_edges) == (31570, 189834)

    # 0 <= m < 192 covers m=0,1 separately and all later m residues.
    # For m>=2, 2^(2m+2) mod96=64 (Lean-certified by Agent41).
    target = {
        ((2 * j + 3) % 96,
         (pow(2, 2 * m + 2, 96) * (j + 3) - j - 3 * m - 5) % 96)
        for j in range(96) for m in range(192)
    }
    assert len(target) == 1536

    mixed_absent = set()
    m32_absent = set()
    for a, k in target:
        if not mixed_seen[mixed_index((a, k, 0))]:
            mixed_absent.add((a, k))
        # A mixed96 residue class includes arbitrary +96 lifts.
        # For a or k <8, q_B8M32 may change after the first lift.
        # Since 96 is a multiple of 32, these four checks cover all lifts.
        if all(not m32_seen[m32_index(q32((aa, kk, 0)))]
               for aa in (a, a + 96) for kk in (k, k + 96)):
            m32_absent.add((a, k))

    extra = mixed_absent - m32_absent
    print(f'mixed96: {mixed_count} seen, {mixed_edges} edges')
    print(f'B8/M32: {m32_count} seen, {m32_edges} edges')
    print(f'second-target residue cells: {len(target)}')
    print(f'mixed96 absent: {len(mixed_absent)}')
    print(f'B8/M32 absent: {len(m32_absent)}')
    print(f'both absent: {len(mixed_absent & m32_absent)}')
    print(f'only mixed96 absent: {len(extra)} {sorted(extra)}')
    print(f'only B8/M32 absent: {len(m32_absent - mixed_absent)}')
    assert len(mixed_absent) == 673
    assert len(m32_absent) == 736
    assert len(mixed_absent & m32_absent) == 669
    assert len(m32_absent - mixed_absent) == 67
    assert extra == {(13, 31), (29, 79), (61, 79), (77, 31)}


if __name__ == '__main__':
    compare()
