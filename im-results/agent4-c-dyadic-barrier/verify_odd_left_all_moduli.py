"""Constructive checks for the uniform odd-first-counter Machine C paper theorem.

Run directly from this directory with Python 3.11+.
Only modular arithmetic is used for enormous stopping inputs; no huge power
is materialized. Original bounce rules are interpreted for small examples.
The checker is corroborating evidence, not a formal proof or a blank-root halt.
"""
from math import gcd
from random import Random

from verify_all_moduli import factor, phi


def order4(p: int) -> int:
    """Compute the multiplicative order of 4 modulo prime p efficiently."""
    order = p - 1
    for q, _ in factor(order):
        while order % q == 0 and pow(4, order // q, p) == 1:
            order //= q
    return order


def root_mod(u: int, n: int, modulus: int) -> int:
    return ((u + 2) * (pow(4, n, modulus) - 1) - 3 * n) % modulus


def construct_exponent(u: int, modulus: int) -> int:
    """Find n>=1 with (u+2)*(4**n-1)-3*n divisible by modulus."""
    if u < 0 or modulus < 1:
        raise ValueError("u must be nonnegative and modulus positive")

    factors = dict(factor(modulus))
    e, j = factors.get(2, 0), factors.get(3, 0)
    two, three = 2**e, 3**j
    residue = (-(u + 2) * pow(3, -1, two)) % two if two > 1 else 0
    lift = (-residue * pow(two, -1, three)) % three if three > 1 else 0
    n = residue + two * lift
    stride = two * three
    while n < max(1, e):
        n += stride
    previous = stride
    odd_part = three
    assert root_mod(u, n, previous) == 0

    for p, exponent in sorted(factors.items()):
        if p < 5:
            continue
        R = previous * phi(odd_part) * order4(p)
        assert gcd(R, p) == 1
        for k in range(exponent):
            pk = p**k
            modulo = pk * p
            assert pow(4, R * pk, modulo) == 1
            value = root_mod(u, n, modulo)
            assert value % pk == 0
            digit = (value // pk) * pow(3 * R, -1, p) % p
            n += R * pk * digit
            assert root_mod(u, n, modulo) == 0
            assert root_mod(u, n, previous) == 0
        previous *= p**exponent
        odd_part *= p**exponent

    assert previous == modulus
    assert root_mod(u, n, modulus) == 0
    return n


def bounce(k: int, c: int) -> tuple[int, int] | None:
    """The exact successful-output branches of Agent46.BounceCalc.bounce."""
    while True:
        if c < 4:
            return None
        if k % 2:
            if c <= 2 * k + 6:
                return (2 * k + 6 - c, c)
            k, c = 2 * k + 3, c - (2 * k + 3)
        else:
            if c == 4:
                return (2 * k + 2, 3)
            if c == 5:
                return None
            if c <= 2 * k + 8:
                return (2 * k + 8 - c, c - 1)
            k, c = 2 * k + 4, c - (2 * k + 5)


def source_odd_step(u: int, K: int) -> tuple[int, int] | None:
    """The original secNext branches for odd first input a=2*u+1."""
    a = 2 * u + 1
    if a == 1:
        if K == 0:
            return (5, 1)
        if K == 1:
            return (2, 3)
        if K == 2:
            return (2, 5)
        if K == 3:
            return (0, 7)
        return bounce(4, 2 * K - 3)
    if K == 0:
        return (a - 2, 2)
    if 2 * K <= a:
        return (a - 2 * K, 2 * K + 2)
    return bounce(a - 1, 2 * K - a + 3)


def main() -> None:
    rng = Random(417456)
    cases = [(u, m) for m in range(1, 501) for u in range(21)]
    cases += [(rng.randrange(10**6), rng.randrange(1, 10**7)) for _ in range(200)]
    cases += [
        (2**50 + 3, 2**20 * 3**6 * 5**4 * 7**3),
        (3**30 + 8, 2**25 * 3**7 * 5**3 * 7**2 * 11**2),
    ]
    biggest_bits = 0
    for u, modulus in cases:
        n = construct_exponent(u, modulus)
        assert root_mod(u, n, modulus) == 0
        biggest_bits = max(biggest_bits, n.bit_length())

    for u in range(21):
        for n in range(1, 9):
            K = (u + 2) * (4**n - 1) - 3 * n + 1
            assert K >= 1 and source_odd_step(u, K) is None

    print(f"PASS: {len(cases)} modular witnesses for all odd first counters")
    print("PASS: 168 direct original-branch synthetic stop checks")
    print(f"Largest witness exponent bit length: {biggest_bits}")


if __name__ == "__main__":
    main()
