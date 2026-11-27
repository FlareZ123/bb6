#!/usr/bin/env python3
"""Exact integer regression for the 19-adic Space Needle cancellation tower.
No floating point, no external packages; finite audit, not an all-depth proof.
"""


def geo(a: int, b: int, n: int, m: int) -> int:
    """sum_{i=0}^{n-1} a^(n-1-i) b^i modulo m in O(log n)."""
    if n == 0:
        return 0
    if n == 1:
        return 1
    half = geo(a, b, n // 2, m)
    doubled = half * (pow(a, n // 2, m) + pow(b, n // 2, m)) % m
    return doubled if n % 2 == 0 else (a * doubled + pow(b, n - 1, m)) % m


def feeder_mod(r: int, k: int) -> int:
    assert r >= 1 and k >= 1
    m = 19 ** k
    period2 = 18 * 19 ** (k - 1)
    # Since 9^r is odd, division by two after reduction modulo 2*period2
    # gives the exact exponent residue for a_r = (9^r+5)/2.
    exponent = ((pow(9, r, 2 * period2) + 5) // 2) % period2
    A = pow(2, exponent, m)
    P = (A - 3) * geo(A * A % m, 9, r, m) % m
    return pow(2, (exponent - 1) % period2, m) * P % m


def inverse_target(k: int) -> int:
    m = 19 ** k
    L = 16
    S = 24 * sum(pow(L, k - 1 - j, m) * pow(19, j, m) for j in range(k)) % m
    return S * pow(pow(L, k, m), -1, m) % m


def direct_integer_feeder(r: int) -> int:
    a = (9 ** r + 5) // 2
    A = 2 ** a
    P = 0
    for j in range(r):
        P = A * A * P + (9 ** j) * (A - 3)
    return 2 ** (a - 1) * P


assert [feeder_mod(r, 1) for r in range(1, 10)] == [1, 15, 0, 7, 10, 0, 11, 13, 0]
assert inverse_target(1) == 11
for r in range(1, 5):
    direct = direct_integer_feeder(r)
    for k in range(1, 4):
        assert direct % (19 ** k) == feeder_mod(r, k)

r = 7
for k in range(1, 13):
    modulus = 19 ** k
    period = 9 * 19 ** (k - 1)
    target = inverse_target(k)
    assert feeder_mod(r, k) == target
    print(f"k={k:2d} residue={r:>18} period={period:>18} shifted_target={target}")
    bigger = 19 ** (k + 1)
    delta = (feeder_mod(r + period, k + 1) - feeder_mod(r, k + 1)) % bigger
    assert delta == 12 * modulus, (k, delta, 12 * modulus)
    diff = (inverse_target(k + 1) - feeder_mod(r, k + 1)) % bigger
    assert diff % modulus == 0
    digit = (diff // modulus) * 8 % 19
    r += period * digit
    assert feeder_mod(r, k + 1) == inverse_target(k + 1)
assert r % 9 == 7
print("PASS: direct polynomial check, complete nine-class base, 12 exact Hensel lifts")
