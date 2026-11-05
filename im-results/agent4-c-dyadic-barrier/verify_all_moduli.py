"""Independent exact modular-integer sanity check for AllFiniteModuliBarrier.md.

Checks 1302 positive moduli with a CRT + increasing-prime-order lifting
algorithm. This is computational corroboration, not a proof of BB(6) or of
any blank-origin halt; see the paper derivation for the universal claim.
"""
from math import gcd
from random import Random


def factor(n: int) -> list[tuple[int, int]]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            a = 0
            while n % d == 0:
                n //= d
                a += 1
            out.append((d, a))
        d = 3 if d == 2 else d + 2
    if n > 1:
        out.append((n, 1))
    return out


def phi(n: int) -> int:
    out = n
    for p, _ in factor(n):
        out = out // p * (p - 1)
    return out


def order4(p: int) -> int:
    order, power = 1, 4 % p
    while power != 1:
        order += 1
        power = power * 4 % p
    return order


def construct_exponent(M: int) -> int:
    fs = dict(factor(M))
    e, j = fs.get(2, 0), fs.get(3, 0)
    even_mod, odd_mod = 2**e, 3**j
    residue = (-pow(3, -1, even_mod)) % even_mod if even_mod > 1 else 0
    coefficient = (
        (1 - residue) * pow(even_mod, -1, odd_mod) % odd_mod
        if odd_mod > 1 else 0
    )
    n = residue + even_mod * coefficient
    while n < max(2, e):
        n += even_mod * odd_mod
    old_mod = even_mod * odd_mod

    def F_mod(modulus: int) -> int:
        return (pow(4, n, modulus) - 3 * n - 1) % modulus

    assert F_mod(old_mod) == 0

    for p, exponent in sorted(fs.items()):
        if p < 5:
            continue
        R = old_mod * phi(odd_mod) * order4(p)
        assert gcd(R, p) == 1
        for k in range(exponent):
            prime_power = p ** (k + 1)
            shift = R * p**k
            assert pow(4, shift, prime_power) == 1
            value = F_mod(prime_power)
            assert value % (p**k) == 0
            multiplier = (value // p**k) * pow(3 * R, -1, p) % p
            n += shift * multiplier
            assert F_mod(prime_power) == 0
            assert F_mod(old_mod) == 0
        odd_mod *= p**exponent
        old_mod *= p**exponent

    assert n >= 2
    assert F_mod(M) == 0
    return n


def main() -> None:
    rng = Random(417456)
    cases = list(range(1, 1001))
    cases += [rng.randrange(1, 10**7) for _ in range(300)]
    cases += [
        2**20 * 3**6 * 5**4 * 7**3,
        2**25 * 3**7 * 5**3 * 7**2 * 11**2,
    ]
    for M in cases:
        n = construct_exponent(M)
        assert (pow(4, n, M) - 3 * n - 1) % M == 0
    print(f"PASS: {len(cases)} constructive modular halting-input certificates")
    print("Largest witness exponent bit length:", max(construct_exponent(M).bit_length() for M in cases))


if __name__ == "__main__":
    main()
