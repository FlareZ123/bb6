"""Conservative exact affine predecessor arithmetic for the P1 GAncestor relation."""
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

    def __mul__(self, k):
        return Aff(self.a * k, self.c * k)

    def div(self, k):
        assert self.a % k == 0 and self.c % k == 0
        return Aff(self.a // k, self.c // k)

    def floor(self, k):
        assert self.a % k == 0
        return Aff(self.a // k, self.c // k)

    def mod(self, k):
        return self.c % k if self.a % k == 0 else None

    def ge(self, minimum=0):
        # t = 7*X-(q+1), X >=32*(q+1), so t >=223.
        return self.a >= 0 and self.a * 223 + self.c >= minimum


def gap(e):
    """Conservative strict interval 14*2^j*X < a*t+c < 14*2^(j+1)*X."""
    a, c = e.a, e.c
    for j in range(1, 17):
        low = 14 * (1 << j)
        high = 2 * low
        d, f = 7 * a - low, high - 7 * a
        if d > 0 and f > 0 and 32*d-a >= 0 and 32*d-a+c > 0 and 32*f+a > c:
            return j
    return None


def inv(b, d):
    """Exhaust source GAncestor inverses, or return None when parity is not uniform."""
    if b.mod(4) != 0:
        return None
    k = b.div(4) - 1
    u = d + b.div(2)
    result = []
    for _ in range(64):
        if not u.ge(2):
            return None
        result.append((k, u))
        parity = u.mod(2)
        if parity is None:
            return None
        if parity == 0:
            return result
        u = (u - 3).div(2)
        if u.a % 2:
            return None
        k = k + u.floor(2) + 1
    return None
