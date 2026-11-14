"""Finite audits for the exact 3-adic law at the deepest Sheep P-node.

The all-parameter proof is in README.md.  For each family and exact
t = v_3(N_r(k))-10, the map from k in the exact-valuation cylinder to the
normalized unit (Y_r(k)+12)/3**(10-e_r+t) is a bijection modulo 3**m.
This script checks that bijection and the resulting distribution of
H_r(k)=v_3(x_{L_r(k)}(k)-1) on finite residue rings.
"""

from collections import Counter
from fractions import Fraction

SCALE = 17496
DELTA = 1102248
Q = 10
# (r, exponent offset, additive numerator constant, odd denominator part,
#  denominator 3-valuation, baseline P-depth)
FAMILIES = (
    (29, 10, 25220, 43, 4, 3),
    *((r, 11, 680296, 1, 10, 0) for r in (8, 17, 26, 35, 44, 53, 62)),
)


def v3_mod(n: int, precision: int) -> int:
    """Return min(v_3(n), precision), using only n modulo 3**precision."""
    if n == 0:
        return precision
    value = 0
    while value < precision and n % 3 == 0:
        value += 1
        n //= 3
    return value


def family_data(family, t: int, precision: int):
    r, offset, constant, odd_denominator, e, baseline = family
    modulus_unit = 3**precision
    period = 3 ** (t + precision)
    valuation_scale = 3 ** (Q + t)
    modulus = valuation_scale * modulus_unit
    inverse_denominator = pow(odd_denominator, -1, modulus_unit)
    exponent0 = SCALE * r + offset
    depth = baseline + t // 2
    units = []
    endpoint_orders = Counter()

    for k in range(period):
        numerator = (pow(2, exponent0 + DELTA * k, modulus) + constant) % modulus
        if numerator % valuation_scale != 0:
            continue
        if numerator % (3 * valuation_scale) == 0:
            continue

        normalized = (numerator // valuation_scale * inverse_denominator) % modulus_unit
        units.append(normalized)

        # x_L + 12 = 8**L * 3**(t mod 2) * normalized.
        # Thus x_L - 1 = 8**L * 3**(t mod 2) * normalized - 13.
        endpoint_minus_one = (
            pow(8, depth, modulus_unit)
            * (3 if t % 2 else 1)
            * normalized
            - 13
        ) % modulus_unit
        endpoint_orders[v3_mod(endpoint_minus_one, precision)] += 1

    expected_units = set(range(1, modulus_unit, 3))
    assert len(units) == len(expected_units), (r, t, precision, len(units))
    assert len(set(units)) == len(units), (r, t, precision, "duplicate unit")
    assert set(units) == expected_units, (r, t, precision, "unit image")

    total = 2 * 3 ** (precision - 1)
    expected_orders = Counter()
    if t % 2:
        expected_orders[0] = total
    else:
        expected_orders[0] = 3 ** (precision - 1)
        for h in range(1, precision):
            expected_orders[h] = 2 * 3 ** (precision - h - 1)
        expected_orders[precision] = 1
    assert endpoint_orders == expected_orders, (
        r, t, precision, endpoint_orders, expected_orders
    )
    return total, endpoint_orders


def run() -> None:
    assert DELTA == 56 * 3**9
    assert (pow(2, DELTA, 3**Q) - 1) % 3**Q == 0
    assert (pow(2, DELTA, 3 ** (Q + 1)) - 1) % 3 ** (Q + 1) == 3**Q

    for family in FAMILIES:
        r, offset, constant, odd_denominator, e, baseline = family
        denominator = 3**e * odd_denominator
        assert (pow(2, SCALE * r + offset, 3**Q) + constant) % 3**Q == 0
        assert odd_denominator % 3 != 0
        assert denominator == (3483 if r == 29 else 59049)
        assert baseline == (3 if r == 29 else 0)

        for t in range(5):
            for precision in range(1, 5):
                total, orders = family_data(family, t, precision)
                assert total == 2 * 3 ** (precision - 1)
        print(
            f"r={r:2d}: exact-t density 2/3^(t+1); "
            "conditional deepest-endpoint law verified"
        )

    # Summing exact t strata gives Pr[t even]=3/4 and Pr[t odd]=1/4.
    assert sum((Fraction(2, 3 ** (2*m + 1)) for m in range(20)), Fraction()) == (
        Fraction(3, 4) * (1 - Fraction(1, 9**20))
    )
    assert sum((Fraction(2, 3 ** (2*m + 2)) for m in range(20)), Fraction()) == (
        Fraction(1, 4) * (1 - Fraction(1, 9**20))
    )

    # The exact unconditional law: H=0 has mass 5/8, and H=h>=1 has
    # mass 1/(4*3**(h-1)); the remaining tail tends to zero geometrically.
    for h in range(1, 12):
        assert Fraction(1, 4 * 3 ** (h - 1)) == Fraction(3, 4 * 3**h)
    assert Fraction(1, 4) + Fraction(3, 8) == Fraction(5, 8)
    print("PASS: all 8 families, t=0..4, precision=1..4.")
    print("Exact law: Pr[H=0]=5/8; Pr[H=h]=1/(4*3^(h-1)) for h>=1.")
    print("Tail: Pr[H>=h]=1/(8*3^(h-2)) for h>=1.")


if __name__ == "__main__":
    run()
