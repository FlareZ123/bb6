#!/usr/bin/env python3
"""Exact finite genuine Sheep first-even blank-orbit quotient coverage.

This is a finite computation on the source-matched even-section return map.
It does not imply nonhalting of the infinite machine or determine BB(6).
"""
from hashlib import sha256
from struct import pack

MODULUS = 1 << 15
EXPECTED_LAST_INDEX = 157868
EXPECTED_SHA = "62e4c30f24fcf82bf42734abaaa9bccd73f99b9e5ecfd3724b12af27d9d91e95"


def first_even_return(t: int) -> int:
    assert t >= 6 and t % 2 == 0
    a = (t & -t).bit_length() - 1
    odd = t >> a
    assert odd >= 3
    z = t + a + (3 if odd == 3 else (odd - 1) // 2)
    h = ((z - 1) & -(z - 1)).bit_length() - 1
    value = 1 + pow(3, h) * ((z - 1) >> h)
    assert value > t and value % 2 == 0
    return value


def main() -> None:
    assert __debug__, "Run without -O so assertions execute"
    first = [-1] * (MODULUS // 2)
    x = 10
    covered = 0
    last = None
    for k in range(EXPECTED_LAST_INDEX + 1):
        assert x & (x - 1), ("unexpected terminal power", k)
        residue = (x % MODULUS) // 2
        if first[residue] < 0:
            first[residue] = k
            covered += 1
            if covered == len(first):
                last = k
                break
        x = first_even_return(x)
    assert last == EXPECTED_LAST_INDEX
    assert x.bit_length() == 126782 and x.bit_count() == 63573
    assert len(set(first)) == MODULUS // 2
    assert max(first) == EXPECTED_LAST_INDEX
    digest = sha256(b"".join(pack("<I", i) for i in first)).hexdigest()
    assert digest == EXPECTED_SHA
    print("PASS: all even residues modulo", MODULUS, "visited")
    print("Last new residue at blank-orbit section index", last)
    print("Full coverage", covered, "/", MODULUS // 2)
    print("Counter bit length on last new visit:", x.bit_length())
    print("First-visit index list SHA256:", digest)


if __name__ == "__main__":
    main()
