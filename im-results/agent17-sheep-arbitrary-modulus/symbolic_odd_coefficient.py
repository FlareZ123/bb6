"""Exact certificates for an arbitrary-coefficient Sheep inverse-family tail.

For Y(j)=(c*2^(j+s)+b)/d, d odd >0, every generic predecessor
valuation is below the rigorously proved cutoff in GENERAL-TAIL.md.
"""
from random import Random


def tail_cutoff(c: int, b: int, d: int) -> int:
    assert c > 0 and d > 0 and d % 2 == 1
    a = 0
    while True:
        k = d * (2 * a - 1) - 2 * b
        modulus = (1 << (a + 1)) + 1
        if k > c and modulus > c * (c + k) + k and modulus >= 2 * d * (c + 1) + 1:
            return a
        a += 1


def parent(c: int, s: int, b: int, d: int, a: int) -> tuple[int, int, int, int]:
    two_a = 1 << a
    return (c, s + a + 1,
            2 * two_a * b + two_a * d * (1 - 2 * a),
            d * (2 * two_a + 1))


def section_step(x: int) -> int | None:
    a = (x & -x).bit_length() - 1
    u = x >> a
    if u == 1:
        return None
    if u == 3:
        return x + a + 3
    return x + a + (u - 1) // 2


def verify() -> None:
    all_checked = 0
    for c in range(1, 24):
        for b in (-23, -7, -1, 0, 5, 13, 41):
            for d in (1, 3, 5, 9):
                a0 = tail_cutoff(c, b, d)
                for a in range(a0, a0 + 12):
                    k = d * (2 * a - 1) - 2 * b
                    modulus = (1 << (a + 1)) + 1
                    assert c < k
                    assert modulus > c * (c + k) + k
                    assert modulus >= 2 * d * (c + 1) + 1
                    # 2^(a+1)=-1 mod modulus: length 2(a+1) is a period.
                    assert all(c * pow(2, n, modulus) % modulus != k
                               for n in range(2 * (a + 1)))
                    all_checked += 1
    rng = Random(17062026)
    for _ in range(20000):
        c = rng.randint(1, 100)
        s = rng.randint(0, 10)
        d = rng.randrange(1, 30, 2)
        a = rng.randint(0, 20)
        j = rng.randint(1, 15)
        u = rng.randrange(5, 90, 2)
        x = (1 << a) * u
        y = section_step(x)
        b = d * y - c * (1 << (j + s))
        pc, ps, pb, pd = parent(c, s, b, d, a)
        assert pd * x == pc * (1 << (j + ps)) + pb
        assert (c * (1 << (j + s + 1)) - (d * (2 * a - 1) - 2 * b)) % (d * ((1 << (a + 1)) + 1)) == 0
    print(f"PASS: {all_checked} infinite-tail hypotheses and exact residue-cycle checks; 20000 exact generic-parent identities")
    for c in (1, 3, 5, 7, 9, 15, 31):
        print(f"coefficient c={c}: b=0,d=1 valuations a<{tail_cutoff(c, 0, 1)}")


if __name__ == '__main__':
    verify()
