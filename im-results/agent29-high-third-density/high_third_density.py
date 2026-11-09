"""Finite rational certificate for Machine C high-stopping third-image density.

Depends mathematically on the exact source inverse and eventual three-image
periodicity established (paper level) by agent45-c-three-step. This script
recomputes the parity-refined tables and independently tests the pullback to
high-stopping parameters. No blank-origin simulation is assumed.
"""
from fractions import Fraction


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def in_i1(x: int, y: int) -> bool:
    return y % 2 == 0 or (x + y) % 4 in (0, 3)


def in_i2(smod: int, ymod: int) -> bool:
    """Exact eventual H2 criterion, copied algebraically from Agent34/45."""
    s = 256 + smod % 64
    y = 64 + ymod % 64
    x = s - y
    q = s + s % 2
    depth = v2(q)
    if depth >= 5:
        return True
    if y % 2 == 0 and in_i1(s - 2, (y - 2) // 2):
        return True
    for n in range(depth - 1):
        if (n + 1 if s % 2 == 0 else n) % 2 != x % 2:
            continue
        a = q // 2 ** (n + 1) - (2 if s % 2 == 0 else 3)
        num = s + y - a - 7 - 3 * n
        assert a >= 2 and num > a and num % 2 == 0
        if in_i1(a, num // 2):
            return True
    return False


def in_i3(s: int, y: int) -> bool:
    """Source-derived H3 test when q is not a pure power and guards are large."""
    q = s + s % 2
    depth = v2(q)
    assert s >= y + 8 and y >= 512 and q != 2 ** depth
    if y % 2 == 0:
        parent_y = (y - 2) // 2
        if in_i2((s - 2 + parent_y) % 64, parent_y % 64):
            return True
    for n in range(depth - 1):
        if (n + 1 if s % 2 == 0 else n) % 2 != (s - y) % 2:
            continue
        a = q // 2 ** (n + 1) - (2 if s % 2 == 0 else 3)
        num = s + y - a - 7 - 3 * n
        assert a >= 8 and num > a and num % 2 == 0
        k = num // 2
        assert k >= 128
        if in_i2((a + k) % 64, k % 64):
            return True
    return False


def residue_h3(j: int, m: int) -> bool:
    """Paper-level exact periodic test for j>=3,m>=8 high-stop candidates."""
    assert j >= 3 and m >= 8
    s = (j - 3 * m - 2) % (1 << 17)
    y = (-j - 3 * m - 5) % 128
    q = (s + s % 2) % (1 << 17)
    # Agent45 proves every valuation >=10 has three ancestors.
    if q % 1024 == 0:
        return True
    return in_i3((1 << 18) + s, 512 + y)


def report() -> None:
    odd_hits = []
    for v in range(1, 12):
        count = 0
        for u in range(1, 64, 2):
            q = ((1 << 14) + u) << v
            for parity in (0, 1):
                s = q - parity
                for r in range(128):
                    y = 512 + r
                    if (s - y) % 2 == 1 and in_i3(s, y):
                        count += 1
        odd_hits.append(count)
    expected = [1248, 2448, 2796, 3408, 3616,
                3864, 3820, 4000, 4096, 4096, 4096]
    assert odd_hits == expected, (odd_hits, expected)
    i3 = sum((Fraction(odd_hits[v - 1], 4096 * 2 ** v)
              for v in range(1, 10)), Fraction()) + Fraction(1, 512)
    assert i3 == Fraction(65067, 131072)

    # 2048 odd-first-coordinate cells among 64*64 possibilities.
    i1_count = sum(in_i1(s-y, y) for s in range(64)
                   for y in range(64) if (s-y) % 2)
    i2_count = sum(in_i2(s, y) for s in range(64)
                   for y in range(64) if (s-y) % 2)
    i1 = Fraction(i1_count, 2048)
    i2 = Fraction(i2_count, 2048)
    assert i1 == Fraction(3, 4)
    assert i2 == Fraction(153, 256)
    assert i2 - i3 == Fraction(13269, 131072)

    # Compare original large stopping counters against residue lookup.
    # Pure dyadic high-valuation cases are universally admitted in I3.
    cases = 0
    for m in range(8, 72):
        for j in range(3, 136):
            k = (1 << (2*m+2)) * (j+3) - (j+3*m+5)
            s = k + 2*j+3
            assert (k+j+3*m+5) % (1 << 17) == 0
            actual = True if v2(s+s%2) >= 10 else in_i3(s, k)
            assert actual == residue_h3(j, m), (j, m)
            cases += 1

    print("odd-first-coordinate I3 hits by v=1..11:", odd_hits)
    print("eventual I1, I2, I3 densities:", i1, i2, i3)
    print("new I2 minus I3 density:", i2 - i3)
    print("absence of three ancestors:", 1 - i3)
    print("high-stopping residue regression:", cases, "cases")


if __name__ == "__main__":
    report()
