"""17-layer exhaustive inverse-congruence sieve for Sheep's genuine E power gates.

Requires only Python 3.10+. For the exact original-source inverse equation,
all generic high valuations and all special sources are eliminated by stated
uniform inequalities. The remaining finite rows are checked for complete
multiplicative periods, with no sampled or heuristic exponent limit.
"""
from fractions import Fraction

SCALE = 17496
MAX_STRATUM = 16
BASE_PERIOD = 63


def gap_threshold(h):
    d = 3 ** h
    for a in range(1, 100):
        k = d * (2 * a - 3) + 2 ** (h + 1)
        if 1 < k < 2 ** a and 2 ** a >= 2 * d:
            return a
    raise AssertionError(("missing generic odd gap", h))


def multiplicative_order_of_delta(modulus, delta):
    """Find q with 2^(delta*q)=1 modulo odd modulus, checking every step."""
    base = pow(2, delta, modulus)
    z = 1
    for q in range(1, 1000):
        z = z * base % modulus
        if z == 1:
            return q
    raise AssertionError(("missing complete period", modulus, delta))


def exceptional_uniform_check():
    """These base inequalities exclude all odd-cofactor-3 sources at s<=16."""
    for h in range(8 + MAX_STRATUM + 1):
        d = 3 ** h
        # a>=100: 0<R(a)<2^a and R(a+1)=R(a)+d; induction applies.
        assert 0 < d * 102 + 2 ** h < 2 ** 100
        assert d < 2 ** 100
        # a<100: every left side <2^140, while j>=17496.
        assert 3 * d * 2 ** 99 + d * 101 + 2 ** h < 2 ** 140
    assert 140 < SCALE


def certify_stratum(s):
    """n=3^s*(r+63*k), 3∤r. Return root-free r from full congruence periods."""
    period_n = BASE_PERIOD * 3 ** s
    delta_j = SCALE * period_n
    rows = []
    for h in range(9 + s):
        d = 3 ** h
        for a in range(1, gap_threshold(h)):
            modulus = d * (2 ** (a + 1) + 1)
            k_res = (d * (2 * a - 3) + 2 ** (h + 1)) % modulus
            q = multiplicative_order_of_delta(modulus, delta_j)
            rows.append((h, a, modulus, k_res, q))
    zero = []
    active = {}
    for r in range(1, 64):
        if r % 3 == 0:
            continue
        j0 = SCALE * 3 ** s * r
        survivors = []
        for h, a, modulus, k_res, q in rows:
            z = pow(2, j0 + h + 1, modulus)
            step = pow(2, delta_j, modulus)
            for t in range(q):
                if z == k_res:
                    survivors.append((h, a))
                    break
                z = z * step % modulus
        if survivors:
            active[r] = survivors
        else:
            zero.append(r)
    assert len(zero) + len(active) == 42
    return rows, zero, active


def main():
    exceptional_uniform_check()
    count = []
    for s in range(MAX_STRATUM + 1):
        rows, zero, active = certify_stratum(s)
        assert all(h <= s + 8 for h, a, _, _, _ in rows)
        assert all(q <= 43 for _, _, _, _, q in rows)
        assert len(zero) in (8, 10, 12, 20, 25, 30)
        count.append(len(zero))
        print(f"s={s:2d}: {len(zero):2d} classes / 42,"
              f" {len(rows)} low generic rows, max period"
              f" {max(q for _, _, _, _, q in rows):2d}; r={zero}")
    assert count == [30, 30, 12, 30, 30, 30, 12, 12, 30, 12,
                     25, 25, 10, 20, 20, 20, 8]
    density = sum((Fraction(v, BASE_PERIOD * 3 ** s)
                   for s, v in enumerate(count)), Fraction())
    assert density == Fraction(1849545554, 2711943423)
    print("Certified lower density among exponent indices 17496*n:",
          f"{density.numerator}/{density.denominator} = {float(density):.11%}")
    print("Unclassified 3-adic tail density <=", float(Fraction(1, 3 ** 17)))
    print("PASS: each class certified for every k by its complete multiplicative period")


if __name__ == "__main__":
    main()
