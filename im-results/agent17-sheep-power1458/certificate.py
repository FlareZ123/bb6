"""Exact all-parameter certificate for the seventh Sheep 3-adic stratum.

Classifies every generic even predecessor of 2^(1458*t), t>=1, 3 not dividing t.
All modular calculations use Python integers and complete multiplicative periods.
"""
from fractions import Fraction
from math import gcd

Q = (
    (2,), (2, 1, 4, 5), (2, 1, 4, 5, 2, 7),
    (2, 1, 4, 5, 2, 7, 8, 1),
    (2, 1, 4, 5, 2, 7, 8, 1, 10, 11),
    (2, 1, 4, 5, 2, 7, 8, 3, 10, 11, 4, 13),
    (2, 3, 4, 5, 2, 7, 8, 9, 10, 11, 4, 13, 14, 15),
    (2, 9, 4, 15, 2, 21, 8, 27, 10, 33, 4, 39, 14, 45, 16, 51),
)
SURVIVORS = {
    (1, 1): (2, 1), (1, 3): (4, 2), (3, 1): (2, 1),
    (3, 6): (7, 5), (5, 1): (2, 1), (7, 1): (2, 1),
    (7, 2): (9, 1), (7, 4): (15, 8),
}
PRIOR_E = (
    *((r, 4860) for r in (138, 402, 1218, 1738)),
    (118, 14580), (246, 24300), (558, 8100), (846, 8100),
    (702, 11340), (194, 24300), (5054, 24300), (366, 8100),
    (1986, 8100), (374, 8100), (1994, 8100), (482, 43740),
    (9230, 43740), (495, 43740), (9243, 43740), (819, 14580),
    (3735, 14580), (188, 55080), (190, 306180), (220, 55080),
    (262, 53460), (442, 1837080), (624, 29160), (648, 122472),
)

def order_two(m: int) -> int:
    residue, period = 1, 0
    while True:
        residue = 2 * residue % m
        period += 1
        if residue == 1:
            return period

def even_return(x: int) -> tuple[int, int]:
    a = (x & -x).bit_length() - 1
    u = x >> a
    assert a >= 1 and u >= 5 and u % 2 == 1
    f = x + a + (u - 1) // 2
    z = f - 1
    h = (z & -z).bit_length() - 1
    return 1 + 3**h * (z >> h), h

def certify() -> None:
    # LTE: v_3(2^(1458*t)-1)=7 for every t not divisible by 3.
    assert pow(2, 1458, 3**7) == 1
    assert pow(2, 1458, 3**8) == 2188
    rows = representatives = max_period = 0
    found = {}
    for h, periods in enumerate(Q):
        d = 3**h
        cutoff = 2 if h == 0 else 2*h + 3
        assert len(periods) == cutoff - 1
        K = lambda a: d*(2*a-3) + 2**(h+1)
        assert 1 < K(cutoff) < 2**cutoff
        assert 2**cutoff >= 2*d
        for a, cycle in enumerate(periods, 1):
            modulus = d*(2**(a+1)+1)
            order = order_two(modulus)
            assert order // gcd(order, 1458) == cycle, (h, a, order)
            assert pow(2, 1458*cycle, modulus) == 1
            matches = [r for r in range(cycle)
                       if pow(2, 1458*r+h+1, modulus) == K(a) % modulus]
            expected = SURVIVORS.get((h, a))
            assert matches == ([] if expected is None else [expected[1]]), (h,a,matches)
            if expected is not None:
                assert expected[0] == cycle
                found[h, a] = modulus, K(a), cycle
            rows += 1
            representatives += cycle
            max_period = max(max_period, cycle)
    assert found.keys() == SURVIVORS.keys()
    assert (rows, representatives, max_period) == (71, 593, 51)
    for (h, a), (cycle, residue) in SURVIVORS.items():
        t = residue
        assert t >= 1 and t % 3 != 0
        modulus = 3**h*(2**(a+1)+1)
        k = 3**h*(2*a-3)+2**(h+1)
        u, rem = divmod(2**(1458*t+h+1)-k, modulus)
        assert rem == 0 and u >= 5 and u % 2 == 1
        target, hidden = even_return(2**a*u)
        assert target == 2**(1458*t) and hidden == h
    for h in range(8):
        D, S = 3**h, 2**h
        e = (3*D).bit_length()-1
        assert e <= h+5 and 2**e < 3*D < 2**(e+1)
        assert D <= 2187 and S <= 128
    assert 2**1452 > 2187*(1452+9)+128
    excluded = [t for t in range(1260)
                if t%3 != 0 and t%4 == 0
                and t%7 != 5 and t%9 != 1 and t%15 != 8]
    assert len(excluded) == 132 and 4 in excluded
    assert Fraction(len(excluded),1458*1260) == Fraction(11,153090)
    assert len(PRIOR_E) == 28
    assert all((1458*t-base) % gcd(1458*1260, period) != 0
               for t in excluded for base, period in PRIOR_E)
    assert all(
        pow(2,1458*4+h+1,3**h*(2**(a+1)+1))
        != (3**h*(2*a-3)+2**(h+1))%(3**h*(2**(a+1)+1))
        for h, periods in enumerate(Q)
        for a in range(1,len(periods)+1)
    )
    print("PASS: 71 generic valuation rows, 593 complete-period representatives, max cycle 51")
    print("PASS: exactly eight generic direct-parent sectors; all others excluded")
    print("PASS: every surviving sector has a genuine exact even-return witness")
    print("PASS: exceptional cofactor-three sources excluded by uniform exponential gap")
    print("PASS: 132 blank-root-free exponent residues modulo 1,837,080")
    print("PASS: disjoint from all 28 earlier explicit E-cone progressions")
    print("Density among exponent indices: 11/153090")

if __name__ == "__main__":
    certify()
