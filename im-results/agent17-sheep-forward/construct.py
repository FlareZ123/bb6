"""Construct genuine h=0 Sheep even-return edges between arbitrary 3-power residues.

All arithmetic is exact. Synthetic input states need not be blank-reachable.
"""
from random import Random


def forward(x):
    assert x >= 5
    a = (x & -x).bit_length() - 1
    u = x >> a
    if u == 1:
        return None
    return x + a + (3 if u == 3 else (u - 1) // 2)


def synthetic_edge(k, r, s):
    q = 3 ** k
    assert k >= 1 and 0 <= r < q and 0 <= s < q
    target = (2 * (s - r) + 1) % q
    b = (2 * s + 1) % 3
    if b == 0:
        b = 3
    for j in range(1, k):
        modulus = 3 ** (j + 1)
        for d in range(3):
            z = b + d * 3 ** j
            f = (4 * z + r * pow(4, -z, modulus)) % modulus
            if f == target % modulus:
                b = z
                break
        else:
            raise AssertionError((k, r, s, j, "no lift"))
    assert (4 * b + r * pow(4, -b, q)) % q == target

    u0 = (r * pow(4, -b, q)) % q
    u = u0 + q * ((1 - u0) * pow(q, -1, 4) % 4)
    if u < 5:
        u += 4 * q
    x = pow(4, b) * u
    z = forward(x)
    assert z is not None and z % 2 == 0
    assert x % q == r and z % q == s
    assert (x & -x).bit_length() - 1 == 2 * b
    return b, u, x, z


def main():
    count = 0
    for k in range(1, 5):
        q = 3 ** k
        for r in range(q):
            for s in range(q):
                synthetic_edge(k, r, s)
                count += 1
        print("EXHAUSTIVE", k, q, "pairs", q * q, flush=True)

    rng = Random(20261103)
    for k in range(5, 9):
        q = 3 ** k
        for _ in range(1000):
            r = rng.randrange(q)
            s = rng.randrange(q)
            synthetic_edge(k, r, s)
            count += 1
        print("RANDOM", k, q, "pairs", 1000, flush=True)

    print("PASS", count, "correct pairs")
    for k, r, s in [(1, 1, 2), (3, 10, 14), (5, 7, 50), (7, 10, 2)]:
        b, u, x, z = synthetic_edge(k, r % (3 ** k), s % (3 ** k))
        print("WITNESS", k, r, s, "valuation", 2 * b, "odd-part", u,
              "source_bits", x.bit_length(), "target_bits", z.bit_length())


if __name__ == "__main__":
    main()
