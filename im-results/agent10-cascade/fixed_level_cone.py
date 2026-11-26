#!/usr/bin/env python3
"""Exact bounded-level inverse cone for machine #746's reset grammar.
See FixedLevelWindow.md for the one-free-ray theorem. No rooted decision follows.
"""
from collections import Counter
from dataclasses import dataclass, replace
from math import gcd
import argparse
import time

def fatal(k: int) -> int:
    return (4 << k) - k - 4

def level(h: int) -> int:
    k = max(0, h.bit_length() - 3)
    while h >= fatal(k + 1):
        k += 1
    while h < fatal(k):
        k -= 1
    return k

def constants(g: int) -> tuple[int, int, int]:
    if g == 0:
        return 0, 0, 0
    d = 3 ** (2 * g)
    s = (4 * d).bit_length()
    t = g * (s + 1)
    m = 4 * g + g * s + d.bit_length() + t.bit_length() + 1
    return s, m + 3, 2 * m + 2 * g + 12

def log2_mod3pow(x: int, d: int) -> tuple[int, int] | None:
    """Return the unique j modulo phi(d) with 2**j == x mod d; d=3**a."""
    if d == 1:
        return 0, 1
    if x % 3 == 0:
        return None
    j, order, q = (0 if x % 3 == 1 else 1), 2, 3
    while q < d:
        q *= 3
        j = next(j + t * order for t in range(3) if pow(2, j + t * order, q) == x % q)
        order *= 3
    return j, order

@dataclass(frozen=True, slots=True)
class Family:
    """(p + q*2**j)/den, for lo<=j<=hi and j=residue (mod modulus)."""
    p: int
    q: int
    den: int
    lo: int
    hi: int
    residue: int
    modulus: int
    level: int

    def count(self) -> int:
        first = self.lo + (self.residue - self.lo) % self.modulus
        return max(0, (self.hi - first) // self.modulus + 1)

    def heights(self):
        for j in range(self.lo + (self.residue - self.lo) % self.modulus, self.hi + 1, self.modulus):
            x = self.p + (self.q << j)
            assert x % self.den == 0
            yield x // self.den

    def restrict(self):
        """Enforce strict source band and integrality for the current node."""
        k = self.level
        d = self.den
        a = -self.q
        assert a > 0
        low = max(1, -((d * (fatal(k + 1) - 1) - self.p) // a))
        high = (self.p - d * (fatal(k) + 1)) // a
        if high < low:
            return None
        lo = max(self.lo, (low - 1).bit_length())
        hi = min(self.hi, high.bit_length() - 1)
        if lo > hi:
            return None
        g = gcd(a, d)
        if self.p % g:
            return None
        d2 = d // g
        if d2 == 1:
            r, m = self.residue, self.modulus
        else:
            target = (-self.p // g) * pow(self.q // g, -1, d2) % d2
            sol = log2_mod3pow(target, d2)
            if sol is None:
                return None
            r, m = sol
            small = min(m, self.modulus)
            if (r - self.residue) % small:
                return None
            if m < self.modulus:
                r, m = self.residue, self.modulus
        out = replace(self, lo=lo, hi=hi, residue=r, modulus=m)
        return out if out.count() else None

    def cross(self, k: int, a: int):
        m = 3 ** a
        d = self.den * m
        return Family(
            ((2 * self.p + 5 * self.den) << a) - ((8 << k) + k + 5) * d,
            self.q << (a + 1), d, self.lo, self.hi,
            self.residue, self.modulus, k,
        ).restrict()

    def even(self, j: int):
        if j == 0:
            return self
        t = (8 << self.level) + self.level
        return replace(self, p=(1 - (1 << j)) * t * self.den + (self.p << j), q=self.q << j).restrict()

def crossing_parents(u: int, K: int, lower: int):
    """Every exact lower-level parent; no simulation or valuation cutoff."""
    if K > lower:
        k = K - 1
        h = 2 * u - (8 << k) - k
        if fatal(k) < h < fatal(k + 1):
            yield h, k
    x = 2 * u + 5
    a = 0
    while x % 3 == 0 and a < 2 * (K - lower):
        x //= 3
        a += 1
        y = x << a
        k = max(0, y.bit_length() - 4)
        if lower <= k < K:
            h = y - (8 << k) - k - 5
            if fatal(k) < h < fatal(k + 1):
                yield h, k

def same_ray(u: int, k: int) -> tuple[int, int, int]:
    t = (8 << k) + k
    d = t - u
    assert d > 0
    v = (t - fatal(k) - 1) // d
    return t, d, max(0, v.bit_length() - 1)

def compressed_cone(u: int, lower: int):
    """Yield disjoint arithmetic-progressive families of all ancestors."""
    N = level(u)
    if not 0 <= lower <= N:
        raise ValueError('lower level must be between zero and target level')
    g = N - lower
    s, r, threshold = constants(g)
    if g and lower < threshold:
        raise ValueError(f'lower level {lower} is below sufficient threshold {threshold}')

    def cross_symbolic(f: Family, early=False):
        K = f.level
        for k in range(lower, K):
            delta = K - k
            a0 = 0 if delta == 1 and not early else 1
            for a in range(a0, 2 * delta + 1):
                child = f.cross(k, a)
                if child is not None:
                    yield from symbolic(child)

    def symbolic(f: Family):
        for j in range(s):
            child = f.even(j)
            if child is None:
                break
            yield child
            yield from cross_symbolic(child)
        else:
            assert f.even(s) is None, 'one-free-ray theorem contradicted'

    def fixed(u: int, K: int):
        t, d, J = same_ray(u, K)
        f = Family(t, -d, 1, 0, J, 0, 1, K)
        yield f
        if K == lower:
            return
        if J >= r:
            early = replace(f, hi=J-r)
            yield from cross_symbolic(early, early=True)
        for j in range(max(0, J-r+1), J+1):
            v = t - (d << j)
            for h, k in crossing_parents(v, K, lower):
                yield from fixed(h, k)

    yield from fixed(u, N)

def brute_cone(u: int, lower: int) -> set[int]:
    """Independent all-valuation and all-source-level enumeration."""
    N = level(u)
    seen = {u}
    stack = [(u, N)]
    while stack:
        v, K = stack.pop()
        parents = []
        for k in range(lower, K + 1):
            h = 2 * v - (8 << k) - k
            if fatal(k) < h < fatal(k + 1):
                parents.append((h, k))
        x, a = 2 * v + 5, 0
        while x % 3 == 0:
            x //= 3
            a += 1
            y = x << a
            for k in range(lower, K + 1):
                h = y - (8 << k) - k - 5
                if fatal(k) < h < fatal(k + 1):
                    parents.append((h, k))
        for h, k in parents:
            assert h < v and level(h) == k
            if h not in seen:
                seen.add(h)
                stack.append((h, k))
    return seen

def regression():
    import random
    rng = random.Random(746)
    cases = total = maxfamilies = 0
    for g in range(1, 10):
        _, _, k0 = constants(g)
        for n in [k0+g,k0+g+1,k0+g+6,1000+g,2000+g]:
            for u in [fatal(n),fatal(n+1)-1,rng.randrange(fatal(n),fatal(n+1))]:
                fs=list(compressed_cone(u,n-g))
                hs=[h for f in fs for h in f.heights()]
                assert len(hs)==len(set(hs)) and set(hs)==brute_cone(u,n-g)
                cases+=1
                total+=len(hs)
                maxfamilies=max(maxfamilies,len(fs))
    print('seed 746, cases',cases,'ancestors',total,'max families',maxfamilies)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('n', type=int)
    p.add_argument('gap', type=int)
    p.add_argument('--check', action='store_true')
    p.add_argument('--regression', action='store_true')
    a = p.parse_args()
    if a.regression:
        regression()
        return
    u = fatal(a.n)
    lo = a.n - a.gap
    start = time.perf_counter()
    fam = list(compressed_cone(u, lo))
    count = Counter()
    for f in fam:
        count[f.level] += f.count()
    elapsed = time.perf_counter()-start
    print('level', a.n, 'gap', a.gap, 'families', len(fam), 'ancestors', sum(count.values()), 'counts', [count[k] for k in range(a.n, lo-1,-1)], 'seconds', round(elapsed,6))
    if a.check:
        heights = [h for f in fam for h in f.heights()]
        assert len(heights) == len(set(heights)), 'duplicate path encoding'
        assert set(heights) == brute_cone(u, lo), 'compressed cone differs from full enumeration'
        print('full exact ancestor-set comparison passed')

if __name__ == '__main__':
    main()
