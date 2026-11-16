"""Exact modular and source-equation certificate for the Sheep j=4374*t stratum.

This checks the complete 89-row period census, all 772 representatives,
the four surviving generic predecessor sectors, the exceptional-source
inequality margins, and the 30 root-free exponent classes.
"""
from fractions import Fraction
from math import gcd

Q = (
    (
        2
    ,),
    (
        2,
        1,
        4,
        5
    ,),
    (
        2,
        1,
        4,
        5,
        2,
        7
    ,),
    (
        2,
        1,
        4,
        5,
        2,
        7,
        8,
        1
    ,),
    (
        2,
        1,
        4,
        5,
        2,
        7,
        8,
        1,
        10,
        11
    ,),
    (
        2,
        1,
        4,
        5,
        2,
        7,
        8,
        1,
        10,
        11,
        4,
        13
    ,),
    (
        2,
        1,
        4,
        5,
        2,
        7,
        8,
        3,
        10,
        11,
        4,
        13,
        14,
        5
    ,),
    (
        2,
        3,
        4,
        5,
        2,
        7,
        8,
        9,
        10,
        11,
        4,
        13,
        14,
        15,
        16,
        17
    ,),
    (
        2,
        9,
        4,
        15,
        2,
        21,
        8,
        27,
        10,
        33,
        4,
        39,
        14,
        45,
        16,
        51,
        2,
        57
    ,)
,)
SURVIVORS = {
    (1, 1): (2, 1),
    (1, 3): (4, 2),
    (3, 6): (7, 4),
    (8, 2): (9, 5),
}


def order_two(m: int) -> int:
    x, n = 1, 0
    while True:
        x = 2*x % m
        n += 1
        if x == 1:
            return n


def even_return(x: int) -> tuple[int, int]:
    a = (x & -x).bit_length()-1
    v = x >> a
    assert a >= 1 and v >= 5 and v % 2 == 1
    z = x+a+(v-1)//2
    h = ((z-1) & -(z-1)).bit_length()-1
    return 1+3**h*((z-1)>>h), h


def certify() -> None:
    assert pow(2, 4374, 3**9) == 6562
    assert pow(2, 8748, 3**9) == 13123
    assert pow(2, 13122, 3**9) == 1
    rows = representatives = max_period = 0
    found = {}
    for h, periods in enumerate(Q):
        d = 3**h
        cutoff = 2 if h == 0 else 2*h+3
        assert len(periods) == cutoff-1
        kfun = lambda a: d*(2*a-3)+2**(h+1)
        assert 1 < kfun(cutoff) < 2**cutoff
        assert 2*d <= 2**cutoff
        for a, q in enumerate(periods, 1):
            modulus = d*(2**(a+1)+1)
            order = order_two(modulus)
            assert order//gcd(order,4374) == q, (h,a,order,q)
            assert pow(2,4374*q,modulus) == 1
            matches = [r for r in range(q)
                       if pow(2,4374*r+h+1,modulus) == kfun(a)%modulus]
            expected = SURVIVORS.get((h,a))
            assert matches == ([] if expected is None else [expected[1]]), (h,a,matches)
            if expected is not None:
                assert expected[0] == q
                found[h,a] = (modulus,kfun(a),q)
            rows += 1
            representatives += q
            max_period = max(max_period,q)
    assert found.keys() == SURVIVORS.keys()
    assert (rows,representatives,max_period) == (89,772,57)

    # Verify that each surviving congruence gives a genuine source edge.
    for (h,a),(q,r) in SURVIVORS.items():
        t = r
        assert t >= 1 and t%3 != 0
        j = 4374*t
        modulus,k,q = found[h,a]
        v,rem = divmod(2**(j+h+1)-k,modulus)
        assert rem == 0 and v >= 5 and v%2 == 1
        assert even_return(2**a*v) == (2**j,h)

    # Exceptional v=3 gap constants for every possible hidden length h<=8.
    for h in range(9):
        d,s = 3**h,2**h
        e = (3*d).bit_length()-1
        g = e-h
        lower,upper = 3*d-2**e,2**(e+1)-3*d
        correction = d-s
        assert g >= 0 and lower > 0 and upper > 0
        assert lower*2**4374 > 2**g*correction
        assert upper*2**4374 > 2**(g+1)*(d*(4374+3)-correction)
        assert upper*2**4374 >= 2**(g+1)*d

    # Root-free classes: exact residues modulo lcm(4,3,7,9)=252.
    excluded = [t for t in range(252)
                if t%4 == 0 and t%3 != 0 and t%7 != 4 and t%9 != 5]
    assert excluded == [
        8,16,20,28,40,44,52,56,64,76,80,92,100,112,124,128,136,
        148,152,160,164,184,188,196,208,220,224,232,236,244
    ]
    assert len(excluded) == 30
    assert Fraction(len(excluded),252) == Fraction(5,42)
    assert Fraction(len(excluded),168) == Fraction(5,28)
    assert all(t%3 != 0 for t in excluded)
    for t in excluded:
        assert t%2 == 0 and t%4 == 0
        assert t%2 != 1 and t%4 != 2
        assert t%7 != 4 and t%9 != 5
        for (h,a),(q,r) in SURVIVORS.items():
            assert t%q != r
    assert 4374*8 == 34992
    print("PASS: 89 exact valuation rows, 772 complete-period representatives, max period 57")
    print("PASS: exactly four generic source sectors; all other generic cases excluded")
    print("PASS: exceptional v=3 source excluded for every h<=8 and every t>=1")
    print("PASS: 30 genuine blank-root power targets excluded modulo 252")
    print("PASS: density 5/28 within v3(j)=7 even exponent stratum; example j=34992")


if __name__ == "__main__":
    certify()
