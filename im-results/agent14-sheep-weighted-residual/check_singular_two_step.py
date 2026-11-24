#!/usr/bin/env python3
"""Reproduce the finite congruence tables for the two singular S=0 families.

The infinite H>=9 tail is Lean-proved in ThreeAdicLTE.lean. This script checks
the finite H=1..8 residue computations and the two sharp witnesses.
"""
from __future__ import annotations


def order_of_two(modulus: int) -> int:
    x = 1
    for n in range(1, 10_000_000):
        x = (2 * x) % modulus
        if x == 1:
            return n
    raise RuntimeError(f"order search exhausted for modulus {modulus}")


def type1_solutions(h: int) -> tuple[int, list[int]]:
    modulus = 135 * 3**h
    period = order_of_two(modulus)
    target = 5 * 3**h
    solutions = [
        b for b in range(period)
        if (pow(2, h, modulus) * (pow(2, b, modulus) - 1) - target) % modulus == 0
    ]
    return period, solutions


def type3_mod3(h: int) -> tuple[int, list[int]]:
    modulus = 3 ** (h + 2)
    period = 2 * 3 ** (h + 1)
    step = 2 * 3 ** (h - 1)
    solutions = [
        b for b in range(step, period + 1, step)
        if (pow(2, h, modulus) * (pow(2, b, modulus) - 1) - 19 * 3**h) % modulus == 0
    ]
    return period, solutions


def type3_mod_prime(h: int, p: int) -> tuple[int, list[int]]:
    period = order_of_two(p)
    solutions = [
        b for b in range(period)
        if (pow(2, h, p) * (pow(2, b, p) - 1) - 19 * 3**h) % p == 0
    ]
    return period, solutions


def main() -> None:
    print("type I: 3^h(5+135k)=2^h(2^B-1)")
    for h in (1, 2):
        period, solutions = type1_solutions(h)
        assert solutions == ([32] if h == 1 else [300])
        print(f"  H={h}: B = {solutions[0]} (mod {period})")

    print("type II: 3^h(19+1683k)=2^h(2^B-1)")
    for h in range(1, 9):
        p3, s3 = type3_mod3(h)
        p11, s11 = type3_mod_prime(h, 11)
        p17, s17 = type3_mod_prime(h, 17)
        assert len(s3) == 1
        combined = []
        if len(s11) == 1 and len(s17) == 1:
            combined = [
                b3 + p3*t for t in range(20)
                if (b3 := s3[0]) >= 0
                and (b3 + p3*t) % 10 == s11[0]
                and (b3 + p3*t) % 8 == s17[0]
            ]
        assert combined == ([11502] if h == 5 else [])
        print(
            f"  H={h}: mod 3^(H+2): B={s3[0]} (mod {p3}); "
            f"mod 11: {s11 or 'none'} (mod {p11}); "
            f"mod 17: {s17 or 'none'} (mod {p17}); "
            f"combined: {combined or 'none'}"
        )

    # At H=5, the three congruences combine to the least positive exponent 11502.
    candidates = [
        b for b in range(1, 29_160)
        if b % 1458 == 1296 and b % 10 == 2 and b % 8 == 6
    ]
    assert candidates == [11502]

    # Sharpness of the two lower bounds.
    assert (2**32 - 1) % 3 == 0
    k1 = (2 * (2**32 - 1) // 3 - 5) // 135
    assert k1 == 21_209_715
    assert 3 * (5 + 135 * k1) == 2 * (2**32 - 1)
    assert (5 + 135 * k1) % 2 == 0 and (5 + 135 * k1) % 4 != 0

    # Keep the very large H=5 witness in quotient form; it has 3,459 decimal digits.
    assert (2**11502 - 1) % 3**5 == 0
    k2_num = 2**5 * (2**11502 - 1) // 3**5 - 19
    assert k2_num % 1683 == 0
    k2 = k2_num // 1683
    assert k2 > 0
    assert 3**5 * (19 + 1683 * k2) == 2**5 * (2**11502 - 1)
    assert (19 + 1683 * k2) % 2**6 != 0
    print(f"sharp witnesses: H=1,B=32,k={k1}; H=5,B=11502,k has {len(str(k2))} digits")


if __name__ == "__main__":
    main()
