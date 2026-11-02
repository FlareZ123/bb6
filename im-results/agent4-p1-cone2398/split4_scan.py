"""Exact-affine refinement for n=262144*q+r, n in the residual P1 sectors.

This is a conservative symbolic scanner. Its closures are computational
certificates, NOT Lean theorems. It reuses source scanner's Aff operators.
The new parameter is s=7*2^(n-16)/4-q; it is integral for all r>=34.
"""
from collections import Counter
from uniform_scan import Aff


def check(r, max_depth=16, max_nodes=2000):
    h = 4

    def positive(v, minimum=0):
        # X=2^(262144*q+r-16) >= 32*h*(q+r+1), hence s >= 223+224*r.
        return v.a >= 0 and v.a * (223 + 224 * r) + v.c >= minimum

    def power_gap(v):
        # v=A*s+C; 14*2^e*X < v < 14*2^(e+1)*X.
        for e in range(1, 19):
            low = 14 * (1 << e)
            upper = 2 * low
            d = 7 * v.a - h * low
            f = h * upper - 7 * v.a
            if (d > 0 and f > 0 and 32 * d - v.a >= 0
                    and 32 * d * (r + 1) + v.c > 0
                    and 32 * f * (r + 1) - v.c > 0):
                return True
        return False

    def ancestors(b, d):
        if b.residue(4) != 0:
            return None
        k = b.divide_exact(4) - 1
        u = d + b.divide_exact(2)
        answers = []
        for _ in range(64):
            if not positive(u, 2):
                return None
            answers.append((k, u))
            p = u.residue(2)
            if p is None:
                return None
            if p == 0:
                return answers
            u = (u - 3).divide_exact(2)
            if u.a % 2:
                return None
            k = k + u.floor_divide(2) + 1
        return None

    stack = [(Aff(524288, -2 * r - 16), Aff(0, 3), 0)]
    seen = set()
    counts = Counter()
    while stack:
        b, d, depth = stack.pop()
        if (b, d) in seen or len(seen) >= max_nodes or depth > max_depth:
            return False, "limit", len(seen), counts
        seen.add((b, d))
        if (b.residue(4) != 0 or not positive(b, 8)
                or d.residue(2) != 1 or not positive(d, 1)):
            return False, "node", len(seen), counts
        branches = ancestors(b, d)
        if branches is None:
            return False, "inverse", len(seen), counts
        for k, u in branches:
            x, y = k * 2 - 4, u + 4
            if not positive(x, 4) or not positive(y, 1):
                return False, "range", len(seen), counts
            parity = y.residue(2)
            if parity == 0:
                if not power_gap(x + 12):
                    return False, "power-gap", len(seen), counts
                counts["power"] += 1
            elif parity == 1 and x.residue(4) == 2:
                counts["mod4"] += 1
            elif parity == 1 and x.residue(4) == 0:
                stack.append((x, y, depth + 1))
            else:
                return False, "parity", len(seen), counts
    return True, "closed", len(seen), counts


if __name__ == "__main__":
    states = Counter()
    fully_closed = 0
    partially_closed = 0
    closures = 0
    for residue in (*range(34, 65536, 16), *range(46, 65536, 16)):
        quarters = []
        for j in range(4):
            closed, status, _, _ = check(residue + 65536 * j)
            quarters.append(closed)
            states[status] += 1
            closures += int(closed)
        fully_closed += all(quarters)
        partially_closed += any(quarters) and not all(quarters)
    print("tested", sum(states.values()))
    print("fully closed base classes", fully_closed)
    print("partially closed base classes", partially_closed)
    print("total closed quarter-classes", closures)
    print("statuses", dict(states))
    assert fully_closed == 5264
    assert partially_closed == 857
    assert closures == 22507
