"""Exact finite Sheep first-even-return witness and synthetic hub checks.

Machine-level soundness of F and E is separately established by the existing
original-source Lean bridge; this script checks a finite authentic prefix.
"""

from hashlib import sha256

TARGET_INDEX = 283344
EXPECTED_SHA = "25377f0e14c813245479e15bcc9a26b1ff75384bbf9417c4e00da0b5b6c289fe"


def valuation_two(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def section_return(x: int) -> int:
    a = valuation_two(x)
    u = x >> a
    assert u >= 3 and u % 2 == 1
    if u == 3:
        y = x + a + 3
    else:
        y = x + a + (u - 1) // 2
        assert 2 * y == (2 ** (a + 1) + 1) * u + 2 * a - 1
    assert y > x
    return y


def first_even_return(x: int, direct_check: bool = False) -> tuple[int, int, int]:
    assert x % 2 == 0
    z = section_return(x)
    h = valuation_two(z - 1)
    w = (z - 1) >> h
    assert w % 2 == 1
    y = 1 + 3**h * w
    assert y > x and y % 2 == 0
    if direct_check:
        t = z
        for _ in range(h):
            assert t % 2 == 1 and t >= 5
            t = section_return(t)
        assert t == y and t % 2 == 0
    return y, h, z


def verify_hubs(x: int, z: int, a: int, h: int) -> None:
    for k in range(1, a + h + 2):
        for n in (1, 3, 5, 17, 255):
            if k <= a:
                assert x % (2**k) == 0
                continue
            L = k - a - 1
            W = (z - 1) >> L
            M = 2 ** (a + 1) + 1
            modulus = 2**k
            coeff = 3**L * M * n
            assert coeff % 2 == 1
            t = (-(1 + 3**L * W) * pow(coeff, -1, modulus)) % modulus
            new_source = x + modulus * n * t
            y, actual_h, _ = first_even_return(new_source)
            assert valuation_two(new_source) == a
            assert new_source % (modulus * n) == x % (modulus * n)
            assert actual_h == L
            assert y % modulus == 0
    print("PASS: 2-adic hub lifts for all k=1..24 and odd n=1,3,5,17,255")


def main() -> None:
    assert section_return(5) == 7 and section_return(7) == 10
    x = 10
    records = {}
    interesting = {0, 1, 20, 121, 646, 989, 1283, 24884, 81103, 87123, TARGET_INDEX}
    for index in range(TARGET_INDEX + 1):
        a = valuation_two(x)
        u = x >> a
        assert u >= 3 and u % 2 == 1
        z = x + a + 3 if u == 3 else x + a + (u - 1) // 2
        h = valuation_two(z - 1)
        y = 1 + 3**h * ((z - 1) >> h)
        if index < 256 or index % 1024 == 0 or index >= TARGET_INDEX - 255:
            assert first_even_return(x, True) == (y, h, z)
        if index in interesting:
            digest = sha256(x.to_bytes((x.bit_length() + 7) // 8, "big")).hexdigest()
            records[index] = (a, h, a + h + 1, x.bit_length(), digest, x % 1_000_000_007)
        if index == TARGET_INDEX:
            assert (a, h, x.bit_length(), x % 1_000_000_007) == (8, 15, 227515, 989231211)
            assert records[index][4] == EXPECTED_SHA
            assert x >> a >= 5
            assert (z - 1) % (2**15) == 0 and (z - 1) % (2**16) != 0
            verify_hubs(x, z, a, h)
        x = y
    for index, (a, h, cap, bits, digest, residue) in records.items():
        print(f"index={index} a={a} h={h} hub_capacity={cap} bits={bits} sha256={digest} mod1e9+7={residue}")
    print(f"PASS: {TARGET_INDEX + 1} genuine finite first-even transitions from 10")


if __name__ == "__main__":
    main()
