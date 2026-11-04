"""Exact finite inverse of the six-state #746 source C-episode model.

This script is a reproducible computational audit, not a proof of infinite
nonhalting.  Formal soundness of the candidate-generator algorithm is in
PreimageCandidates.lean / ReverseCertificate.lean.
"""
from collections import deque


def cstep(a: int, b: int):
    if b == 0:
        return (2, 2 * a + 1)
    if b == 1:
        return None
    d = b - 2
    if d >= 2 * a:
        return (2 * a + 2, d - 2 * a)
    t = 6 * a + d + (8 if d % 2 == 0 else 5)
    return (t // 4, t % 4)


def well(a: int, b: int) -> bool:
    if b in (0, 2):
        return True
    if b % 2 == 0 or (a + 2) % 4:
        return False
    power = (a + 2) // 4
    return power > 0 and (power & (power - 1)) == 0


def predecessors(u: int, v: int):
    """Enumerate all source-C predecessors satisfying the rooted phase invariant."""
    candidate = set()
    if u == 2 and v % 2:
        candidate.add(((v - 1) // 2, 0))
    if (u, v) == (2, 0):
        candidate.add((0, 2))
    if v in (0, 2) and (4 * u + v - 8) % 6 == 0:
        a = (4 * u + v - 8) // 6
        if a >= 1:
            candidate.add((a, 2))
    for m in range((u + 2).bit_length() + 1):
        a = 4 * (1 << m) - 2
        if v % 2:
            candidate.add((a, u + v))
        if v in (0, 2):
            candidate.add((a, 4 * u + v - 6 * a - 3))
    return {
        (a, b) for a, b in candidate if a >= 0 and b >= 0
        and well(a, b) and cstep(a, b) == (u, v)
    }


def verify_bounded(max_a=150, max_b=150):
    actual = {}
    for a in range(max_a):
        for b in range(max_b):
            if well(a, b):
                target = cstep(a, b)
                if target is not None:
                    actual.setdefault(target, set()).add((a, b))
    for target, expected in actual.items():
        got = {s for s in predecessors(*target)
               if s[0] < max_a and s[1] < max_b}
        assert got == expected, (target, got, expected)
    print(f"PASS: {len(actual)} observed C targets, exact inverse enumeration "
          f"for 0<=a<{max_a}, 0<=b<{max_b}")


def reverse_cone(n: int, limit: int = 100000):
    assert n >= 4 and n % 6 in (4, 5)
    target = (4 * (1 << n) - n - 4, 0)
    root = (2, 0)
    queue = deque([(target, 0)])
    seen = {target}
    edges = 0
    depth_max = 0
    while queue and len(seen) <= limit:
        state, depth = queue.popleft()
        depth_max = max(depth_max, depth)
        for p in predecessors(*state):
            edges += 1
            assert 2 * p[0] + p[1] < 2 * state[0] + state[1]
            if p == root:
                return ("ROOT_FOUND", n, len(seen), edges, depth_max)
            if p not in seen:
                seen.add(p)
                queue.append((p, depth + 1))
    return ("COMPLETE" if not queue else "TRUNCATED",
            n, len(seen), edges, depth_max)


if __name__ == "__main__":
    verify_bounded()
    for index in (52, 53, 100, 101, 196, 197, 202, 203, 400):
        print(reverse_cone(index))
