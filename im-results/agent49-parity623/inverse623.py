#!/usr/bin/env python3
"""Complete inverse of the #623 high-level map, using exact flat-drain windows.

All arithmetic is integer. Source pin:
  google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b
See DrainCorrectionGrowth.lean for the generic kernel-checked inverse
window and positive-budget image injectivity. This Python implementation
is a reproducible consumer of those bounds, not itself kernel checked.
"""
from collections import deque
from dataclasses import dataclass


def flat_drain(a: int, b: int, z: int) -> tuple[int, int] | None:
    while b:
        q, r = divmod(b, 3)
        if r == 0:
            a, b, z = a + 1, q - 1, z + 6*q + 3
        elif r == 1:
            if a == 0:
                return None
            a, b, z = a - 1, q, z + 6*q + 7
        elif a == 0:
            b, z = q, z + 6*q + 7
        else:
            a, b, z = a - 1, q + 1, z + 6*q + 5
    return a, z


def next_state(a: int, d: int) -> tuple[int, int] | None:
    if a == 0:
        return flat_drain(d+1, 2, 2) if d % 2 else (d, 7)
    if d % 2 and a >= d+5:
        return flat_drain(a-d-5, d+3, 5)
    if d % 2 == 0 and a >= d+3:
        return flat_drain(a-d-2, d+2, 2)
    if a % 2:
        return None
    if a == d+2:
        return flat_drain(0, a, 2)
    if d % 2:
        return flat_drain(d+4-a, a-1, 3)
    return flat_drain(d+1-a, a+1, 0)


def full_stats(b: int) -> tuple[int, int, int]:
    """(first drift, third excess, flat length), ignoring zero-budget visits."""
    j = e = ell = 0
    while b:
        q, r = divmod(b, 3)
        j += 1 if r == 0 else -1
        e += (0, 4, 2)[r]
        ell += 1
        b = q + r - 1
    return j, e, ell


def image(b: int) -> int:
    return 3*b + full_stats(b)[1]


def window(y: int, z: int, n: int) -> tuple[int, int]:
    """b in [ceil((y-z-4n)/3),floor((y-z)/3)], intersected with Nat."""
    return max(0, (y-z-4*n+2)//3), (y-z)//3


def inverse_image(value: int, parity: int, lo: int, hi: int) -> int | None:
    """Parity-specific binary search; uniqueness is the Lean image theorem."""
    i, j = max(0, (lo-parity+1)//2), (hi-parity)//2
    while i <= j:
        k = (i+j)//2
        b = 2*k+parity
        f = image(b)
        if f == value:
            return b
        if f < value:
            i = k+1
        else:
            j = k-1
    return None


@dataclass(frozen=True)
class Sector:
    name: str
    z: int
    bparity: int
    # (a,d) = (A+b+c_a, b+c_d) or (b+c_a, A+b+c_d)
    left: bool
    c_a: int
    c_d: int

    def restore(self, a0: int, b: int) -> tuple[int, int]:
        if self.left:
            return a0+b+self.c_a, b+self.c_d
        return b+self.c_a, a0+b+self.c_d


SECTORS = (
    Sector("LO", 5, 0, True, 2, -3),
    Sector("LE", 2, 0, True, 0, -2),
    Sector("RO", 3, 1, False, 1, -3),
    Sector("RE", 0, 1, False, -1, -2),
)


def predecessors(target: tuple[int, int], even_only: bool = False) -> list[tuple[int, int]]:
    """Complete inverse for all natural section inputs (or even-first subset).

    Complexity: O(n^3) flat arithmetic operations in the small-first window,
    O(n log n) in the positive-budget window, n=max(1,bit_length(y)).
    The bounds count arithmetic operations; arbitrary-integer bit costs extra.
    """
    x, y = target
    assert x >= 0 and y >= 0
    n = max(1, y.bit_length())
    out: set[tuple[int, int]] = set()

    def accept(a: int, d: int) -> None:
        if a < 0 or d < 0 or (even_only and a % 2):
            return
        if next_state(a, d) == target:
            out.add((a, d))

    # Axis outputs are exact, including their parity conditions.
    if y == 7 and x % 2 == 0:
        accept(0, x)
    if y == 14 and x % 2 == 0:
        accept(0, x+1)

    # Every positive-a successful non-diagonal branch is a bundled flat drain.
    # For x >= 2n, the inverse window forces A >= n, hence all flat steps
    # have positive first counter and the output is (A+J(b),z+F(b)).
    for sector in SECTORS:
        lo, hi = window(y, sector.z, n)
        if hi < lo:
            continue
        if x >= 2*n:
            if (y-sector.z) % 2 != sector.bparity:
                continue
            b = inverse_image(y-sector.z, sector.bparity, lo, hi)
            if b is not None:
                drift, _, _ = full_stats(b)
                A = x-drift
                if A >= n:
                    accept(*sector.restore(A, b))
        else:
            for b in range(lo+(sector.bparity-lo)%2, hi+1, 2):
                for A in range(max(0, x-n), x+n+1):
                    accept(*sector.restore(A, b))

    # The a=d+2 branch has A=0 and can occur only with x<=n.
    if x <= n:
        lo, hi = window(y, 2, n)
        lo = max(2, lo)
        for b in range(lo+(-lo)%2, hi+1, 2):
            accept(b, b-2)
    return sorted(out)


def reverse_closure(target: tuple[int,int], even_only: bool = True, max_nodes: int = 100000):
    """Finite exact tree/graph traversal; callers must honor the cap flag."""
    seen = {target}
    queue = deque([target])
    leaves = set()
    while queue:
        s = queue.popleft()
        pp = predecessors(s, even_only)
        if not pp:
            leaves.add(s)
        for p in pp:
            if p not in seen:
                seen.add(p)
                queue.append(p)
                if len(seen) >= max_nodes:
                    return seen, leaves, False
    return seen, leaves, True


def regression(limit: int = 100) -> None:
    """Exhaustive *target* box, independently generated by forward source map.

    Strict mass growth gives a+d <= x+y-7 <= 2*limit-7 for all parents.
    The check therefore covers both false positives and missing parents.
    """
    targets = {(x,y):set() for x in range(limit+1) for y in range(limit+1)}
    for a in range(2*limit-6):
        for d in range(2*limit-6-a):
            t = next_state(a,d)
            if t in targets:
                targets[t].add((a,d))
    for t, expected in targets.items():
        actual = set(predecessors(t))
        assert actual == expected, (t, sorted(actual), sorted(expected))
        even = set(predecessors(t, True))
        assert even == {p for p in expected if p[0]%2==0}, (t,even,expected)
    print(f"Exact inverse matched forward enumeration for {len(targets):,} targets; even-first subset also matched.")


if __name__ == "__main__":
    regression(120)
