"""All-even-modulus synthetic Sheep first-even quotient witnesses.

Run directly with Python 3. Uses the published generic Sheep section
arithmetic; each graph edge may have a distinct integer representative.
"""
from functools import lru_cache
from math import gcd
from verify_dyadic_complete import parent, decode, encode, even_return


def crt2(a: int, m: int, b: int, n: int) -> int:
    assert gcd(m, n) == 1
    return (a+m*((b-a)*pow(m, -1, n) % n)) % (m*n)


@lru_cache(None)
def order_two(q: int) -> int:
    if q == 1:
        return 1
    n, v = 1, 2 % q
    while v != 1:
        v = (v*2) % q
        n += 1
    return n


def choose_zero_exponent(q: int, r: int, lower: int) -> int:
    """Construct a>=lower with (2+2^(-a))*r+2*a-1 = 0 mod odd q.

    Strong induction on q, descending to gcd(q, ord_q(2)).
    """
    assert q > 0 and q % 2 == 1
    if q == 1:
        return max(1, lower)
    period = order_two(q)
    d = gcd(q, period)
    assert 1 <= d < q
    c = choose_zero_exponent(d, r, 0)
    f = (2+pow(2, -c, q))*r + 2*c-1
    assert f % d == 0
    m = q // d
    t = -((f//d)*pow((2*period)//d, -1, m)) % m if m > 1 else 0
    a = c + t*period
    jump = period*m
    if a < lower:
        a += ((lower-a+jump-1)//jump)*jump
    assert a >= lower and ((2+pow(2, -a, q))*r+2*a-1) % q == 0
    return a


def generic_section(t: int) -> int | None:
    a = (t & -t).bit_length()-1
    u = t >> a
    if u == 1:
        return None
    return t+a+(3 if u == 3 else (u-1)//2)


def direct_even(t: int) -> int | None:
    s = generic_section(t)
    if s is None:
        return None
    while s % 2:
        s = generic_section(s)
        assert s is not None
    return s


def lift_edge(p: int, q: int, source: int, target2: int, a: int, h: int) -> tuple[int, int]:
    """Prescribe source mod 2^p*q and next dyadic residue."""
    m2 = 1 << p
    modulus = m2*q
    assert parent(p, a, h, target2) == source % m2
    ua = (source >> a) % (1 << (p-a))
    ub = source * pow(2, -a, q) % q if q > 1 else 0
    u0 = crt2(ua, 1 << (p-a), ub, q)
    d = (1 << (a+1))+1
    c = d*u0 + 2*a-3
    rem = p-a-h-1
    assert c % (1 << (h+1)) == 0
    w0 = c >> (h+1)
    z0 = 1+3**h*w0
    assert (target2-z0) % (1 << rem) == 0
    scale = 1 << (p-rem)
    slope = 3**h*d*q
    k = (((target2-z0)//(1 << rem))*pow(slope, -1, scale)) % scale
    u = u0+(1 << (p-a))*q*k
    w = w0+d*q*(1 << rem)*k
    while u < 5 or w < 5:
        k += scale
        u = u0+(1 << (p-a))*q*k
        w = w0+d*q*(1 << rem)*k
    assert u % 2 == 1 and w % 2 == 1
    x = (1 << a)*u
    z = 1+3**h*w
    assert x % modulus == source and z % m2 == target2
    assert even_return(x) == z and direct_even(x) == z
    return x, z


def reach_zero_from_dyadic_zero(p: int, q: int, source: int) -> tuple[int, int]:
    """A single generic F-even return to mixed residue zero."""
    m2 = 1 << p
    modulus = m2*q
    assert source % m2 == 0
    a = choose_zero_exponent(q, source, p)
    u0 = crt2((1-2*a) % (2*m2), 2*m2,
              source*pow(2, -a, q) % q if q > 1 else 0, q)
    u = u0
    while u < 5:
        u += 2*m2*q
    x = (1 << a)*u
    z = x+a+(u-1)//2
    assert x % modulus == source and z % modulus == 0
    assert even_return(x) == z and direct_even(x) == z
    return x, z


def outgoing_hub(p: int, q: int, target: int) -> tuple[int, int]:
    """One generic even step from mixed residue zero to target."""
    modulus = (1 << p)*q
    u = 5*q
    c = (u-1)//2
    a = p+(target-p-c) % modulus
    x = (1 << a)*u
    z = x+a+c
    assert x % modulus == 0 and z % modulus == target
    assert even_return(x) == z and direct_even(x) == z
    return x, z


def verify() -> None:
    total = 0
    transitions = 0
    largest = 0
    q_values = (1, 3, 5, 7, 9, 11, 13, 15, 21, 25, 27, 31, 45)
    for p in range(1, 9):
        m2 = 1 << p
        for q in q_values:
            modulus = m2*q
            for source in range(0, modulus, 2):
                word = decode(p, source % m2)
                r = source
                for i, (a, h) in enumerate(word):
                    target2 = encode(p, word[i+1:])
                    x, z = lift_edge(p, q, r, target2, a, h)
                    largest = max(largest, x.bit_length())
                    r = z % modulus
                    transitions += 1
                assert r % m2 == 0
                x, z = reach_zero_from_dyadic_zero(p, q, r)
                assert z % modulus == 0
                largest = max(largest, x.bit_length())
                transitions += 1
                assert len(word)+1 <= p//2+1
                total += 1
            for target in range(0, modulus, 2):
                x, _ = outgoing_hub(p, q, target)
                largest = max(largest, x.bit_length())
            print(f"m={modulus}: {modulus//2} even residues have a witnessed path to zero and a zero-outgoing edge")
    print(f"PASS: {total} mixed residues, {transitions} exact even-return path edges, max witness bits {largest}")


if __name__ == "__main__":
    verify()
