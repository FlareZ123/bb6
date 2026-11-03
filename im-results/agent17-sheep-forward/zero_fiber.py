"""Exact Sheep even-return edges from a zero 2-adic source fiber.

For any k>=1, odd q>=1, source r modulo q, target s modulo q,
and even s2 modulo 2^k, find x divisible by 2^k with the true
generic first-even return E(x) equal to s modulo q and s2 modulo 2^k.
Synthetic witnesses do not imply blank-orbit reachability.
"""
from general_odd import factor, ord4, Pmod
from math import gcd
from random import Random


def root_strided(q, r, c, H):
    assert q % 2 == 1 and H > 0 and gcd(q, H) == 1
    M = 1
    b = 0
    for p, a in factor(q):
        T = H * M * ord4(M)
        d = ord4(p)
        assert gcd(T * d, p) == 1
        for j in range(a):
            L = T * d * p ** j
            for t in range(p):
                z = b + t * L
                if Pmod(r, c, z, p ** (j + 1)) == 0:
                    b = z
                    break
            else:
                raise AssertionError((q, r, c, H, p, j))
            assert b % H == 0
            assert Pmod(r, c, b, M * p ** (j + 1)) == 0
        M *= p ** a
    assert M == q and Pmod(r, c, b, q) == 0
    return b


def zero_edge(k, q, r0, s0, s2):
    assert k >= 1 and q % 2 == 1
    assert 0 <= r0 < q and 0 <= s0 < q
    assert 0 <= s2 < 2 ** k and s2 % 2 == 0
    H = 2 ** (k - 1)
    c = 2 * r0 + 2 * q - 2 * s0 - 1
    b = root_strided(q, r0, c, H)
    B = b + H * q * ord4(q)
    assert B > 0 and 2 * B >= k
    assert 2 * B % (2 ** k) == 0 and Pmod(r0, c, B, q) == 0
    u0 = r0 * pow(4, -B, q) % q
    u2 = (1 + 2 * s2) % (2 ** (k + 1))
    u = u0 + q * ((u2 - u0) * pow(q, -1, 2 ** (k + 1))
                  % (2 ** (k + 1)))
    if u < 5:
        u += q * 2 ** (k + 1)
    assert u >= 5 and u % 4 == 1
    assert u % (2 ** (k + 1)) == u2
    assert pow(4, B, q) * u % q == r0
    assert (2 * B + (u - 1) // 2) % (2 ** k) == s2
    assert (r0 + 2 * B + (u - 1) // 2) % q == s0

    if B < 6000:
        x = pow(4, B) * u
        y = x + 2 * B + (u - 1) // 2
        assert x % (2 ** k) == 0 and x % q == r0
        assert y % (2 ** k) == s2 and y % q == s0 and y % 2 == 0
    return B, u


def main():
    rng = Random(20261103)
    count = 0
    for k in range(1, 9):
        for q in range(1, 52, 2):
            for _ in range(30):
                r = rng.randrange(q)
                s = rng.randrange(q)
                s2 = 2 * rng.randrange(2 ** (k - 1))
                zero_edge(k, q, r, s, s2)
                count += 1
        print("PASS 2-adic zero-fiber", k, "cases", count, flush=True)
    print("COMPLETE", count)


if __name__ == "__main__":
    main()
