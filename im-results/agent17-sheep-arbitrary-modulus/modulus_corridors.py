"""Exact generalized-CRT witnesses for Sheep valuation-zero inverse corridors.

All claims involving 2^j inherit the exact multiplicative-order theorem and
section-edge bridge from Agent 39's original Lean formalization. This script
independently checks the elementary congruence construction and sample edges.
"""
from math import gcd, lcm


def depth_divisor(h: int) -> int:
    assert h >= 1
    return 2 * 3 ** (h - 1)


def persistent_divisor(modulus: int) -> int:
    assert modulus > 0
    t = modulus
    while t % 3 == 0:
        t //= 3
    return modulus // t * gcd(modulus, 2)


def exponent_witness(modulus: int, residue: int, depth: int) -> int | None:
    """Return j>=3 with j%modulus=residue%modulus and depth_divisor(depth)|j.

    Return None exactly if the two congruences are incompatible.
    """
    assert modulus > 0 and depth > 0
    d = depth_divisor(depth)
    r = residue % modulus
    g = gcd(modulus, d)
    if r % g:
        return None
    reduced_modulus = modulus // g
    k = 0 if reduced_modulus == 1 else (
        (r // g) * pow(d // g, -1, reduced_modulus)
    ) % reduced_modulus
    j = d * k
    step = lcm(modulus, d)
    while j < 3:
        j += step
    assert j % modulus == r and j % d == 0 and j >= 3
    return j


def sheep_step(x: int) -> int | None:
    a = (x & -x).bit_length() - 1
    u = x >> a
    if u == 1:
        return None
    if u == 3:
        return 3 * (1 << a) + a + 3
    return x + a + (u - 1) // 2


def verify() -> None:
    trials = 0
    edges = 0
    for modulus in range(1, 181):
        persistent = persistent_divisor(modulus)
        assert modulus % persistent == 0
        for residue in range(modulus):
            for depth in range(1, 8):
                j = exponent_witness(modulus, residue, depth)
                admissible = residue % gcd(modulus, depth_divisor(depth)) == 0
                assert (j is not None) == admissible
                if residue % persistent == 0:
                    assert j is not None
                if j is not None:
                    assert pow(2, j, 3 ** depth) == 1
                    if j <= 2000:
                        u = ((1 << j) - 1) // (3 ** depth)
                        assert u * 3 ** depth + 1 == 1 << j
                        x = 1 + (1 << depth) * u
                        for _ in range(depth):
                            assert x % 2 == 1 and x >= 5
                            x = sheep_step(x)
                        assert x == 1 << j
                        edges += depth
                trials += 1
    print(f"PASS: {trials} residue/depth CRT cases; {edges} genuine Sheep edges checked")
    for modulus in [7, 54, 100, 5400, 10800, 16200]:
        d = persistent_divisor(modulus)
        print(f"modulus={modulus}: persistent classes={modulus // d}/{modulus}, divisor={d}")


if __name__ == "__main__":
    verify()
