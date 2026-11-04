#!/usr/bin/env python3
"""Independent finite premises for universal Sheep E parents of 3*2^a.

The all-a proof is the mathematical derivation in README.md. All code here
uses Python 3.10+ standard library and exact integers.
"""


def order2(m):
    p = 1
    r = 2 % m
    while r != 1:
        r = r * 2 % m
        p += 1
    return p


def even_return(x):
    b = (x & -x).bit_length() - 1
    v = x >> b
    assert b >= 1 and v >= 3 and (v % 2) == 1
    z = x + b + (3 if v == 3 else (v - 1) // 2)
    h = ((z-1) & -(z-1)).bit_length() - 1
    return 1 + pow(3, h) * ((z - 1) >> h)


def exact_parents(y):
    # y=3*2^a => 3 divides y, so every actual incoming E edge has h=0.
    assert y % 3 == 0
    found = []
    for b in range(1, y.bit_length() + 1):
        special = 3 << b
        if special + b + 3 == y:
            assert even_return(special) == y
            found.append(special)
        m = (1 << (b+1)) + 1
        v, rem = divmod(2*y + 1 - 2*b, m)
        if rem == 0 and v >= 5 and (v % 2) == 1:
            x = v << b
            assert even_return(x) == y
            found.append(x)
    return sorted(found)


def expected_parents(a):
    bs = ([1] if a % 4 == 0 else []) + (
        [2] if a % 2 == 1 else []) + (
        [3] if a % 8 == 5 else [])
    return sorted(
        ((3 * 2**(a+1) + 1 - 2*b) // (2**(b+1)+1)) << b
        for b in bs
    )


def main():
    assert __debug__, "Do not use Python -O"
    for b, expected in (
        (1, (0,)),
        (2, (1, 3, 5)),
        (3, (5,)),
        (4, ()),
    ):
        modulus = 2**(b+1)+1
        period = order2(modulus)
        residues = tuple(a for a in range(period) if
                         (3*pow(2,a+1,modulus)-(2*b-1)) % modulus == 0)
        assert residues == expected, (b, period, residues)
        assert pow(2, period, modulus) == 1
        print("PASS b", b, "modulus", modulus, "period", period,
              "allowed exponent residues", residues)

    for b in range(5, 200):
        K = 2*b-1
        assert K % 2 == 1 and 1 < K < 2**b
    print("PASS first 195 high-b Fermat-modulus gap instances; induction in README")

    for a in range(2, 1001):
        assert exact_parents(3*(1<<a)) == expected_parents(a), a
    print("PASS literal exact-source E inverse enumeration for 2<=a<=1000")
    print("Universal theorem is proved on paper; not Lean source-certified")


if __name__ == "__main__":
    main()
