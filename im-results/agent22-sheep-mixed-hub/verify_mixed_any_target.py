"""Direct all-target edge from every dyadically-zero Sheep quotient class.

This implements the generalized multiplicative-order-descent theorem; all
witnesses use legal positive generic F-even Sheep returns.
"""
from math import gcd
from verify_mixed_complete import crt2, order_two, direct_even
from verify_dyadic_complete import even_return


def choose_target_exponent(q: int, r: int, s: int, lower: int) -> int:
    """Solve (2+2^(-a))*r+2a-1-2s=0 mod every odd q."""
    assert q >= 1 and q % 2 == 1
    if q == 1:
        return max(1, lower)
    period = order_two(q)
    d = gcd(q, period)
    assert 1 <= d < q and d % 2 == 1
    c = choose_target_exponent(d, r, s, 0)
    f = (2+pow(2, -c, q))*r + 2*c-1-2*s
    assert f % d == 0
    n = q//d
    k = -((f//d)*pow((2*period)//d, -1, n)) % n if n > 1 else 0
    a = c + k*period
    jump = period*n
    if a < lower:
        a += ((lower-a+jump-1)//jump)*jump
    assert a >= lower
    assert ((2+pow(2, -a, q))*r+2*a-1-2*s) % q == 0
    return a


def direct_to_target(p: int, q: int, source: int, target: int) -> tuple[int, int]:
    """Actual E(x)=z, source x mod 2^p*q and target z mod 2^p*q."""
    assert p >= 1 and q > 0 and q % 2 == 1
    m2 = 1 << p
    modulus = m2*q
    assert source % m2 == 0 and target % 2 == 0
    a = choose_target_exponent(q, source, target, p)
    u = crt2((1+2*(target-a)) % (2*m2), 2*m2,
             source*pow(2, -a, q) % q if q > 1 else 0, q)
    while u < 5:
        u += 2*m2*q
    x = (1 << a)*u
    z = x+a+(u-1)//2
    assert x % modulus == source and z % modulus == target
    assert z % 2 == 0 and even_return(x) == z and direct_even(x) == z
    return x, z


def verify() -> None:
    n = 0
    for p in range(1, 5):
        for q in (1, 3, 5, 7, 9, 11, 13, 15, 21, 25, 27, 31, 45):
            modulus = (1 << p)*q
            step = 2 if modulus <= 128 else max(2, (modulus//64//2)*2)
            targets = range(0, modulus, step)
            for source in range(0, modulus, 1 << p):
                for target in targets:
                    if target % 2 == 0:
                        direct_to_target(p, q, source, target)
                        n += 1
    print(f"PASS: {n} exact independent dyadic-zero -> arbitrary-even-target first-even edges")


if __name__ == "__main__":
    verify()
