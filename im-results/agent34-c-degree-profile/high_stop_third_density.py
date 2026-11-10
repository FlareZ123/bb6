"""Exact arithmetic certificate for Machine C's third-section-image density.

Source: the unmodified secNext inverse grammar in SectionAllInverse.lean,
and Agent34's two-image criterion. The accompanying README proves the
finite-reduction-to-source and the asymptotic counting argument.
"""

from fractions import Fraction


def valuation_two(n: int) -> int:
    return (n & -n).bit_length() - 1


def image_one(a: int, k: int) -> bool:
    return k % 2 == 0 or (a + k) % 4 in (0, 3)


def two_image(s_res: int, k_res: int) -> bool:
    """Agent34's exact H2(sum mod64, right mod64)."""
    s = 256 + s_res % 64
    y = 64 + k_res % 64
    x = s - y
    q = s + s % 2
    v = valuation_two(q)
    if v >= 5:
        return True
    if y % 2 == 0 and image_one(s - 2, (y - 2) // 2):
        return True
    for n in range(v - 1):
        if s % 2 == 0:
            if (n + 1) % 2 != x % 2:
                continue
            a = q // 2 ** (n + 1) - 2
        else:
            if n % 2 != x % 2:
                continue
            a = q // 2 ** (n + 1) - 3
        numerator = s + y - a - 7 - 3 * n
        assert a >= 2 and numerator > a and numerator % 2 == 0
        if image_one(a, numerator // 2):
            return True
    return False


def high_parent_in_two(s: int, y: int, n: int) -> bool:
    """Legal ordinary original-source high parent, then H2 membership."""
    q = s + s % 2
    a = q // 2 ** (n + 1) - (2 if s % 2 == 0 else 3)
    numerator = s + y - a - 7 - 3 * n
    assert n + 2 <= valuation_two(q)
    assert (n + 1 if s % 2 == 0 else n) % 2 == (s - y) % 2
    assert a >= 8 and numerator > a and numerator % 2 == 0
    k = numerator // 2
    assert k >= 128
    return two_image((a + k) % 64, k % 64)


def third_image_generic(s: int, y: int) -> bool:
    """Exact H3 for large coordinates outside pure-power sum diagonals."""
    q = s + s % 2
    v = valuation_two(q)
    assert q != 2 ** v and s >= y + 8 and y >= 512
    if y % 2 == 0:
        a, k = s - 2, (y - 2) // 2
        if two_image((a + k) % 64, k % 64):
            return True
    for n in range(v - 1):
        if (n + 1 if s % 2 == 0 else n) % 2 != (s - y) % 2:
            continue
        if high_parent_in_two(s, y, n):
            return True
    return False


def low_valuation_table():
    rows = []
    mass = Fraction(0)
    for v in range(1, 12):
        hits = 0
        for u in range(1, 64, 2):
            # A large multiple of 64 ensures every source high parent exists.
            q = ((1 << 14) + u) << v
            for parity in (0, 1):
                s = q - parity
                for r in range(128):
                    hits += third_image_generic(s, 512 + r)
        rows.append((v, hits))
        mass += Fraction(hits, 8192 * 2 ** v)
    return rows, mass


def high_valuation_table():
    # Modulo 2^15 decides all four chosen parents' H2 values.
    # v=15 represents every v>=15.
    cases = 0
    for v in range(12, 16):
        for u in range(1, 1 << max(1, 15 - v), 2):
            q = (1 << v) * u
            for parity in (0, 1):
                s = q - parity
                for r in range(128):
                    y = 512 + r
                    depth_choices = range(0 if y % 2 else 1, 8, 2)
                    assert any(high_parent_in_two(s, y, n) for n in depth_choices), (v, u, parity, r)
                    cases += 1
    return cases


def report():
    assert sum(two_image(s, y) for s in range(64) for y in range(64)) == 2448
    rows, low_mass = low_valuation_table()
    assert rows == [
        (1, 2544), (2, 4848), (3, 5628), (4, 6780),
        (5, 7296), (6, 7544), (7, 7700), (8, 8076),
        (9, 8176), (10, 8192), (11, 8192)]
    cases = high_valuation_table()
    assert cases == 2048
    density = low_mass + Fraction(1, 2 ** 11)
    assert density == Fraction(261171, 524288)
    print("V: I3-positive cells / 8192")
    for v, hits in rows:
        print(v, hits, "/ 8192")
    print("High-valuation complete 4-candidate coverage:", cases, "cases")
    print("Exact limiting I3 density:", density, float(density))



# Added by Agent 34, 10 November 2026, reusing Agent45's exact H3 finite
# reduction and original-section predecessor source equations.

def odd_first_counter_census():
    """All v rows conditional on target first counter x=s-y being odd."""
    rows = []
    for v in range(1,12):
        hits = 0
        for u in range(1,64,2):
            q = ((1 << 14) + u) << v
            for parity in (0,1):
                s=q-parity
                for yr in range(128):
                    y=512+yr
                    if (s-y)%2:
                        hits += third_image_generic(s,y)
        rows.append((v,hits))
    return rows


def periodic_high_stop_third_image(j_res: int, m_res: int) -> bool:
    """Valid for ALL high stops m>=8,j>=3, evaluated modulo 2^17."""
    modulus=1 << 17
    s_res=(j_res-3*m_res-2)%modulus
    y_res=(-j_res-3*m_res-5)%128
    # S must be sufficiently large, and pure-power Q have universal H3.
    s=(1 << 18)+s_res
    y=512+y_res
    q=s+s%2
    if valuation_two(q)>=12:
        return True
    return third_image_generic(s,y)


def high_stop_original_coordinates(j: int,m: int):
    k=(1 << (2*m+2))*(j+3)-(j+3*m+5)
    return (2*j+3,k)


def report_high_stop_density():
    expected=[1248,2448,2796,3408,3616,3864,3820,4000,4096,4096,4096]
    rows=odd_first_counter_census()
    assert [hits for _,hits in rows]==expected,rows
    # Every odd-first-coordinate target at valuation>=9 is in I3.
    assert all(hits==4096 for v,hits in rows if v>=9)
    in_third = sum((Fraction(hits, 4096*(1 << v)) for v,hits in rows if v<=8),
                   Fraction(1,1 << 8))
    excluded=1-in_third
    assert in_third == Fraction(65067,131072)
    assert excluded == Fraction(66005,131072)
    # For each m>=8, the high stopping exponent vanishes modulo 2^17.
    # Check the source-based direct third-image predicate on actual target
    # examples independently against the periodic reduction.
    for m in range(8,13):
        for j in range(3,131):
            x,y=high_stop_original_coordinates(j,m)
            assert y>=512 and x>=8
            direct=third_image_generic(x+y,y)
            periodic=periodic_high_stop_third_image(j,m)
            assert direct == periodic,(j,m,x,y,direct,periodic)
    print("Odd-first I3 valuation rows:",rows)
    print("Exact high-stop third-image acceptance density:",in_third)
    print("Exact high-stop third-image exclusion density:",excluded)
    print("All 640 direct original-source high-stop periodicity regressions PASS")


if __name__ == "__main__":
    report()
    report_high_stop_density()
