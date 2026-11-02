"""Conservative exact-affine P1 inverse-cone sieve; candidates require Lean certification."""
from collections import Counter
from dataclasses import dataclass


@dataclass(frozen=True)
class Aff:
    a: int
    c: int

    def __add__(self, other):
        if isinstance(other, int):
            other = Aff(0, other)
        return Aff(self.a + other.a, self.c + other.c)

    __radd__ = __add__

    def __sub__(self, other):
        if isinstance(other, int):
            other = Aff(0, other)
        return Aff(self.a - other.a, self.c - other.c)

    def __mul__(self, factor):
        return Aff(self.a * factor, self.c * factor)

    def divide_exact(self, divisor):
        assert self.a % divisor == self.c % divisor == 0
        return Aff(self.a // divisor, self.c // divisor)

    def floor_divide(self, divisor):
        assert self.a % divisor == 0
        return Aff(self.a // divisor, self.c // divisor)

    def residue(self, modulus):
        return self.c % modulus if self.a % modulus == 0 else None

    def at_least(self, minimum=0):
        # For t=7*X-(q+1), X>=32*(q+1), we know t>=223.
        return self.a >= 0 and self.a * 223 + self.c >= minimum


def adjacent_power_gap(expression):
    """Sufficient integer inequalities for low*X < A*t+C < 2*low*X."""
    a, c = expression.a, expression.c
    for exponent in range(1, 17):
        low = 14 * (1 << exponent)
        high = 2 * low
        d, e = 7 * a - low, high - 7 * a
        if d > 0 and e > 0 and 32 * d - a >= 0:
            if 32 * d - a + c > 0 and 32 * e + a > c:
                return exponent
    return None


def all_positive_g_ancestors(b, d):
    """Exhaust all inverse nests of the source GAncestor inductive relation."""
    if b.residue(4) != 0:
        return None
    k = b.divide_exact(4) - 1
    u = d + b.divide_exact(2)
    ancestors = []
    for _ in range(64):
        if not u.at_least(2):
            return None
        ancestors.append((k, u))
        parity = u.residue(2)
        if parity is None:
            return None
        if parity == 0:
            return ancestors
        u = (u - 3).divide_exact(2)
        if u.a % 2:
            return None
        k = k + u.floor_divide(2) + 1
    return None


def check_residue(r, max_depth=16, max_nodes=2000):
    """Analyze n=65536*q+r for all q>=0. Fail closed if any guard is unknown."""
    assert 21 <= r < 65536 and r % 16 in (2, 14)
    # X=2^(65536*q+r-16); t=7*X-(q+1).
    # H(n)-6 = 131072*t + (131056-2*r).
    stack = [(Aff(131072, 131056 - 2 * r), Aff(0, 3), 0)]
    seen = set()
    leaves = Counter()
    while stack:
        b, d, depth = stack.pop()
        if (b, d) in seen:
            return False, "repeat", len(seen), leaves
        seen.add((b, d))
        if len(seen) > max_nodes or depth > max_depth:
            return False, "limit", len(seen), leaves
        if b.residue(4) != 0 or not b.at_least(8):
            return False, "node", len(seen), leaves
        if d.residue(2) != 1 or not d.at_least(1):
            return False, "node", len(seen), leaves
        inverses = all_positive_g_ancestors(b, d)
        if inverses is None:
            return False, "inverse", len(seen), leaves
        for k, u in inverses:
            x, y = k * 2 - 4, u + 4
            if not x.at_least(4) or not y.at_least(1):
                return False, "range", len(seen), leaves
            parity = y.residue(2)
            if parity == 0:
                if adjacent_power_gap(x + 12) is None:
                    return False, "power_gap", len(seen), leaves
                leaves["power"] += 1
            elif parity == 1 and x.residue(4) == 2:
                leaves["mod4"] += 1
            elif parity == 1 and x.residue(4) == 0:
                stack.append((x, y, depth + 1))
            else:
                return False, "parity", len(seen), leaves
    return True, "closed", len(seen), leaves


if __name__ == "__main__":
    for sector in (2, 14):
        start = 34 if sector == 2 else 30
        closed = []
        status_counts = Counter()
        for residue in range(start, 65536, 16):
            success, status, interior_count, leaves = check_residue(residue)
            status_counts[status] += 1
            if success:
                closed.append((residue, interior_count, leaves["power"], leaves["mod4"]))
        print("sector", sector, "closed", len(closed), "statuses", dict(status_counts))
        print("records: residue, interior, power-leaves, mod4-leaves")
        for record in closed:
            print(*record)
