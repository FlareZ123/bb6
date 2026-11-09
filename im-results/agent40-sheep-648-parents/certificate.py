"""Complete arithmetic certificate for direct Sheep E parents of 2^(648*t).

The exact unbounded proof and physical-machine bridge are in README.md.
Only Python's standard library is needed.
"""
from fractions import Fraction
from math import gcd

SURVIVORS = {(3, 6): (7, 6), (5, 2): (9, 1), (5, 4): (15, 14)}
PRIOR_E = (
    *((r, 4860) for r in (138, 402, 1218, 1738)),
    (118, 14580), (246, 24300), (558, 8100), (846, 8100), (702, 11340),
    (194, 24300), (5054, 24300), (366, 8100), (1986, 8100),
    (374, 8100), (1994, 8100), (482, 43740), (9230, 43740),
    (495, 43740), (9243, 43740), (819, 14580), (3735, 14580),
    (188, 55080), (190, 306180), (220, 55080), (262, 53460),
    (442, 1837080), (624, 29160), (648, 122472),
)

def order_two(m: int) -> int:
    assert m > 1 and m % 2 == 1
    value, period = 1, 0
    while True:
        period += 1
        value = 2 * value % m
        if value == 1:
            return period

def first_even(x: int) -> tuple[int, int, int]:
    a = (x & -x).bit_length() - 1
    v = x >> a
    assert a >= 1 and v >= 3 and v % 2
    z = x + a + (3 if v == 3 else (v-1)//2)
    h = ((z-1) & -(z-1)).bit_length() - 1
    return 1 + 3**h * ((z-1) >> h), a, h

def prove() -> None:
    assert pow(2,648*3,729)==1
    assert [pow(2,648*t,729) for t in range(3)] == [1,244,487]
    rows = representatives = largest_cycle = 0
    actual = {}
    for h in range(6):
        D = 3**h
        C = D - 2**h
        e = (3*D).bit_length()-1
        g = e-h
        L = 3*D - 2**e
        U = 2**(e+1) - 3*D
        assert g >= 0 and L > 0 and U > 0
        assert L * 2**1296 > 2**g*C
        assert U * 2**1296 > 2**(g+1)*(D*(1296+3)-C)
        assert U * 2**1296 >= 2**(g+1)*D
        A = 2 if h==0 else 2*h+3
        K = lambda a: D*(2*a-3)+2**(h+1)
        assert 1<K(A)<2**A and 2**A>=2*D
        for a in range(1,A):
            m = D*(2**(a+1)+1)
            C_eq = 2*a*D+2**(h+1)
            cycle = order_two(m)//gcd(order_two(m),648)
            assert pow(2,648*cycle,m)==1
            matches = [t for t in range(cycle)
                       if (pow(2,h+1+648*t,m)+3*D)%m == C_eq%m]
            expected = SURVIVORS.get((h,a))
            assert matches == ([] if expected is None else [expected[1]]), (h,a,m,matches)
            if expected is not None:
                assert cycle == expected[0]
                actual[(h,a)]=(m,K(a),cycle,expected[1])
            rows += 1
            representatives += cycle
            largest_cycle = max(largest_cycle,cycle)
    assert (rows,representatives,largest_cycle)==(41,246,39)
    assert set(actual)==set(SURVIVORS)
    for h,a,t in ((3,6,6),(5,2,10),(5,4,14)):
        j=648*t
        m,K,cycle,match=actual[(h,a)]
        v,rem=divmod(2**(j+h+1)-K,m)
        assert rem==0 and v>=5 and v%2==1
        x=2**a*v
        target,ah,hh=first_even(x)
        assert target==2**j and (ah,hh)==(a,h)
    good=[t for t in range(315) if t%3!=0 and t%7!=6
          and t%9!=1 and t%15!=14]
    assert len(good)==132 and Fraction(len(good),648*315)==Fraction(11,17010)
    assert all(all((648*t-b)%gcd(648*315,p)!=0 for b,p in PRIOR_E)
               for t in good)
    print('PASS 41 full-period valuation rows, 246 period representatives, max cycle 39')
    print('PASS survivors', actual)
    print('PASS 6 all-a exceptional gap exclusions, high-a cutoffs, exact target v3')
    print('PASS 132 new direct-parent-free exponent classes mod 204120; density 11/17010')
    print('PASS three positive generic source witnesses, disjoint from 28 prior E families')

if __name__ == '__main__':
    prove()
