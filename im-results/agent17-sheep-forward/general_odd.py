"""Construct generic Sheep first-even-return edges for every positive odd modulus.

The witness is an exact transition from a synthetic (not necessarily blank-reachable)
section state. Prime powers are processed in increasing-prime order.
"""
from math import gcd
from random import Random


def factor(n):
    result = []
    p = 3
    while p * p <= n:
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        if a:
            result.append((p, a))
        p += 2
    if n > 1:
        result.append((n, 1))
    return result


def ord4(q):
    if q == 1:
        return 1
    z = 4 % q
    d = 1
    while z != 1:
        z = z * 4 % q
        d += 1
    return d


def Pmod(r, c, b, q):
    return (pow(4, b, q) * ((4 * b + c) % q) + r) % q


def root(q, r, c):
    assert q > 0 and q % 2 == 1
    M = 1
    b = 0
    for p, a in factor(q):
        T = M * ord4(M)
        d = ord4(p)
        assert gcd(T * d, p) == 1
        for j in range(a):
            L = T * d * p ** j
            assert pow(4, L, p ** (j + 1)) == 1
            b0 = b
            for t in range(p):
                cand = b0 + t * L
                if Pmod(r, c, cand, p ** (j + 1)) == 0:
                    b = cand
                    break
            else:
                raise AssertionError((q, r, c, M, p, j, b0, L))
            assert Pmod(r, c, b, M) == 0
            assert Pmod(r, c, b, p ** (j + 1)) == 0
        M *= p ** a
        assert Pmod(r, c, b, M) == 0
    assert M == q and Pmod(r, c, b, q) == 0
    return b


def edge(q, r, s):
    assert q >= 3 and q % 2 == 1 and 0 <= r < q and 0 <= s < q
    c = 2 * r + 2 * q - 2 * s - 1
    b = root(q, r, c)
    T = q * ord4(q)
    B = b + T
    assert B > 0 and pow(4, B, q) == pow(4, b, q)

    u0 = r * pow(4, -B, q) % q
    u = u0 + q * ((1 - u0) * pow(q, -1, 4) % 4)
    if u < 5:
        u += 4 * q
    assert u >= 5 and u % 4 == 1
    assert pow(4, B, q) * u % q == r

    # The generic Sheep formula gives 2E = 2x + 4B + u - 1.
    assert (2 * r + 4 * B + u - 1 - 2 * s) % q == 0

    # Independent exact integer transition check when witness is manageable.
    if B < 10000:
        x = pow(4, B) * u
        y = x + 2 * B + (u - 1) // 2
        assert x % q == r and y % q == s and y % 2 == 0
    return b, B, u


def main():
    rng = Random(20261103)
    count = 0
    for q in range(3, 202, 2):
        for r in range(q):
            edge(q, r, rng.randrange(q))
            count += 1
    print("PASS odd q<=201, all r, one sampled s per r:", count)

    for q in [243, 245, 315, 343, 375, 405, 441, 625, 729,
              945, 1001, 1331, 3125]:
        for _ in range(100):
            edge(q, rng.randrange(q), rng.randrange(q))
            count += 1
    print("PASS larger odd q, seeded samples:", count)


if __name__ == "__main__":
    main()
