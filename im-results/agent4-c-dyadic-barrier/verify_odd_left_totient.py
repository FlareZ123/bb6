"""Independent strong-induction witness algorithm for AllOddFirstModuliBarrier.md.

Constructs n with M | A*(4**n-1)-3*n for any A>=0 and M>=1.
The proof uses the totient period and gcd reduction, not prime lifting.
This deterministic test is numerical corroboration, not a formal proof.
"""
from math import gcd
from random import Random

from verify_all_moduli import factor, phi


def F_mod(A: int, n: int, modulus: int) -> int:
    return (A * (pow(4, n, modulus) - 1) - 3 * n) % modulus


def witness(A: int, modulus: int, minimum_n: int = 1) -> int:
    if A < 0 or modulus < 1 or minimum_n < 0:
        raise ValueError("nonnegative A/minimum and positive modulus required")
    fs = dict(factor(modulus))
    e, j = fs.get(2, 0), fs.get(3, 0)
    two, three = 2**e, 3**j
    B = two * three
    q = modulus // B
    assert gcd(q, 6) == 1

    # First solve 3*n=-A (mod 2**e), n=0 (mod 3**j).
    r = (-A * pow(3, -1, two)) % two if two > 1 else 0
    lift = (-r * pow(two, -1, three)) % three if three > 1 else 0
    n0 = r + two * lift
    threshold = max(e, 1, minimum_n)
    n0 += max(0, (threshold - n0 + B - 1) // B) * B
    assert F_mod(A, n0, B) == 0

    def solve(v: int) -> int:
        if v == 1:
            return n0
        h = phi(v)
        g = gcd(v, h)
        assert 1 <= g < v and gcd(v, 6) == 1
        n = solve(g)
        assert n >= n0 and (n - n0) % B == 0
        assert F_mod(A, n, g) == 0

        R = B * h
        assert pow(4, R, v) == 1
        divisor = gcd(v, 3 * R)
        assert divisor == g
        value = F_mod(A, n, v)
        assert value % divisor == 0
        reduced = v // divisor
        z = (
            (value // divisor)
            * pow((3 * R) // divisor, -1, reduced)
            % reduced
            if reduced > 1 else 0
        )
        out = n + R * z
        assert F_mod(A, out, v) == 0
        assert F_mod(A, out, B) == 0
        return out

    n = solve(q)
    assert n >= threshold and F_mod(A, n, modulus) == 0
    return n


def main() -> None:
    rng = Random(20261105)
    cases = [(A, m) for A in range(35) for m in range(1, 1201)]
    cases += [
        (rng.randrange(10**10), rng.randrange(1, 10**7))
        for _ in range(1000)
    ]
    for A, m in cases:
        n = witness(A, m)
        assert F_mod(A, n, m) == 0
    print(f"PASS: {len(cases)} all-coefficient modular witnesses")

    for A in (0, 1, 2, 3, 300, 2**50):
        for m in (1, 2, 3, 9, 27, 35, 441, 2**15 * 3**5 * 11**3):
            for lower in (1, 1000, 10**6):
                n = witness(A, m, lower)
                assert n >= lower and F_mod(A, n, m) == 0
    print("PASS: all 162 arbitrary-lower-bound checks")


if __name__ == "__main__":
    main()
