"""Arithmetic certificate for the exact direct Sheep E fiber of 2^(486*t).

Every modular period is computed and checked. The unbounded argument and
source-machine correspondence are documented in README.md.
"""
from fractions import Fraction
from math import gcd

Q = (
    (2,),
    (2, 1, 4, 5),
    (2, 1, 4, 5, 2, 7),
    (2, 1, 4, 5, 2, 7, 8, 1),
    (2, 1, 4, 5, 2, 7, 8, 3, 10, 11),
    (2, 3, 4, 5, 2, 7, 8, 9, 10, 11, 4, 13),
    (2, 9, 4, 15, 2, 21, 8, 27, 10, 33, 4, 39, 14, 45),
)
SURVIVORS = {
    (1, 1): (2, 1),
    (1, 3): (4, 2),
    (3, 1): (2, 1),
    (3, 6): (7, 1),
    (5, 1): (2, 1),
    (6, 2): (9, 2),
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
    v = x >> a
    assert a >= 1 and v >= 3 and v % 2 == 1
    z = x + a + (3 if v == 3 else (v - 1) // 2)
    h = ((z - 1) & -(z - 1)).bit_length() - 1
    return 1 + 3**h * ((z - 1) >> h), h


def certify() -> None:
    # LTE gives v3(2^(486t)-1)=6 whenever 3 does not divide t.
    assert pow(2, 486, 3**6) == 1
    assert pow(2, 486, 3**7) == 730
    assert len(PRIOR_E) == 28
    rows, reps, max_period, found = 0, 0, 0, {}
    for h, periods in enumerate(Q):
        d, correction = 3**h, 3**h - 2**h
        cutoff = 2 if h == 0 else 2*h + 3
        assert len(periods) == cutoff - 1
        kfun = lambda a: d*(2*a-3)+2**(h+1)
        assert 1 < kfun(cutoff) < 2**cutoff
        assert 2**cutoff >= 2*d
        e = (3*d).bit_length() - 1
        g, lower, upper = e-h, 3*d-2**e, 2**(e+1)-3*d
        assert g >= 0 and lower > 0 and upper > 0
        assert lower*2**486 > 2**g*correction
        assert upper*2**486 > 2**(g+1)*(d*(486+3)-correction)
        assert upper*2**486 >= 2**(g+1)*d
        for a, period in enumerate(periods, 1):
            modulus = d*(2**(a+1)+1)
            order = order_two(modulus)
            assert order//gcd(order,486) == period, (h, a, order)
            assert pow(2,486*period,modulus) == 1
            matches = [r for r in range(period)
                       if pow(2,486*r+h+1,modulus) == kfun(a)%modulus]
            expected = SURVIVORS.get((h,a))
            assert matches == ([] if expected is None else [expected[1]]), (h,a,matches)
            if expected is not None:
                assert expected[0] == period
                found[h,a] = modulus, kfun(a), period
            rows += 1
            reps += period
            max_period = max(max_period,period)
    assert found.keys() == SURVIVORS.keys()
    assert (rows,reps,max_period) == (55,429,45)
    for (h,a),(period,r) in SURVIVORS.items():
        t = r or period
        assert t >= 1 and t%3 != 0
        modulus = 3**h*(2**(a+1)+1)
        k = 3**h*(2*a-3)+2**(h+1)
        v, remainder = divmod(2**(486*t+h+1)-k,modulus)
        assert remainder == 0 and v >= 5 and v%2 == 1
        y, hidden = even_return(2**a*v)
        assert y == 2**(486*t) and hidden == h
    excluded = [t for t in range(252)
                if t%3 != 0 and t%4 == 0 and t%7 != 1 and t%9 != 2]
    assert len(excluded) == 30 and 4 in excluded
    assert Fraction(len(excluded),486*252) == Fraction(5,20412)
    assert all((486*t-base)%gcd(486*252,period) != 0
               for t in excluded for base,period in PRIOR_E)
    for t in range(1,253):
        if t%3 == 0:
            continue
        actual = sum(pow(2,486*t+h+1,3**h*(2**(a+1)+1))
                     == (3**h*(2*a-3)+2**(h+1))%(3**h*(2**(a+1)+1))
                     for h,qs in enumerate(Q) for a in range(1,len(qs)+1))
        expected = 3*(t%2==1)+(t%4==2)+(t%7==1)+(t%9==2)
        assert actual == expected, (t,actual,expected)
    print('PASS: 55 exact valuation rows, 429 complete-period residues, max period 45')
    print('PASS: six necessary and sufficient generic source sectors')
    print('PASS: seventh exceptional-source gap and all high-a signed-power gaps')
    print('PASS: 30 new root-free exponent residues mod 122472, density 5/20412')
    print('PASS: all classes disjoint from 28 previously listed E-cone progressions')


if __name__ == '__main__':
    certify()
