"""Exact all-index Sheep first-even predecessor exclusion for j=1296+340200*k.

This standard-library certificate covers low-valuation congruences, all
higher valuation cutoffs, exceptional-source magnitude inequalities,
fixed 3-adic target valuation, and prior E-cone disjointness.
The associated README supplies the unbounded mathematical proof.
"""
from math import gcd

BASE, PERIOD = 1296, 340200
PRIOR_E = (
    *((r, 4860) for r in (138, 402, 1218, 1738)),
    (118, 14580), (246, 24300), (558, 8100), (846, 8100),
    (702, 11340),
    (194, 24300), (5054, 24300), (366, 8100), (1986, 8100),
    (374, 8100), (1994, 8100), (482, 43740), (9230, 43740),
    (495, 43740), (9243, 43740), (819, 14580), (3735, 14580),
    (188, 55080), (190, 306180), (220, 55080), (262, 53460),
    (442, 1837080), (624, 29160), (648, 122472),
)

def order_two(m: int) -> int:
    assert m > 1 and m % 2 == 1
    exponent, residue = 0, 1
    while True:
        exponent += 1
        residue = 2 * residue % m
        if residue == 1:
            return exponent

def prove() -> None:
    assert pow(2, BASE, 729) == 487
    assert pow(2, PERIOD, 729) == 1
    assert PERIOD % 5400 == 0
    assert all((BASE - b) % gcd(PERIOD, p) != 0 for b, p in PRIOR_E)

    total_rows, total_reps, peak_cycle = 0, 0, 0
    for h in range(6):
        D = 3**h
        S = h
        C = D - 2**h
        e = (3*D).bit_length()-1
        g = e - S
        L = 3*D - 2**e
        U = 2**(e+1) - 3*D
        assert g >= 0 and L > 0 and U > 0
        assert L * 2**BASE > 2**g * C
        assert U * 2**BASE > 2**(g+1) * (D * (BASE+3) - C)
        assert U * 2**BASE >= 2**(g+1) * D

        A = 2 if h == 0 else 2*h+3
        K = lambda a: D*(2*a-3)+2**(h+1)
        assert 1 < K(A) < 2**A and 2**A >= 2*D
        for a in range(1, A):
            m = D*(2**(a+1)+1)
            target = K(a) % m
            order = order_two(m)
            cycle = order // gcd(order, PERIOD)
            assert pow(2, PERIOD*cycle, m) == 1
            assert all(pow(2, BASE+h+1+PERIOD*t, m) != target
                       for t in range(cycle)), (h,a)
            total_rows += 1
            total_reps += cycle
            peak_cycle = max(peak_cycle,cycle)
    assert (total_rows,total_reps,peak_cycle) == (41,88,13)
    print(f'PASS: {total_rows} valuation rows, {total_reps} period residues, max cycle {peak_cycle}')
    print('PASS: all 6 exceptional-source gaps and high-valuation cutoffs')
    print('PASS: v3(2^j-1)=5; prior E families disjoint')
    print('PROVED: no first-even predecessor of 2^(1296+340200*k) for all k>=0')

if __name__ == '__main__':
    prove()
