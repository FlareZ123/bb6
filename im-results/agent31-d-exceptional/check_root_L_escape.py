"""Audit eleven source-derived D-section formulas against a literal raw TM.

The computed blank-entry section sequences are conditional until the eleven
source macros are combined in a single authenticated infinite-tape proof.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib

from check_second_escape import physical_return


@dataclass(frozen=True)
class L:
    a: int
    q: int = 0
    b: int = 0

    def __post_init__(self) -> None:
        assert self.a >= 2 and self.q >= 0 and self.b >= 0
        assert self.q != 0 or self.b == 0


def next_source_macro(c: L) -> tuple[L | None, str]:
    a, q, b = c.a, c.q, c.b
    if a % 3 == 2:
        k = (a - 2) // 3
        if q == 0:
            return L(8 * k + 9), 'B0'
        if q == 1:
            return L(8 * k + 10 + b), 'B1'
        return L(8 * k + 10, q - 1, b), 'Bq'
    if a % 3 == 0:
        k = (a - 3) // 3
        if q == 0:
            return L(8 * k + 11), 'A0'
        u, r = q - 1, (b + 1) // 3
        d = u + 4 * r
        if (b + 1) % 3 == 0:
            return L(8 * k + 11 + 2 * d), 'Aa'
        if (b + 1) % 3 == 1:
            return L(8 * k + 13 + 2 * d), 'Ab'
        return L(8 * k + 7 + 2 * d, 1, 5), 'Ac'
    k = (a - 4) // 3
    if q == 0:
        return L(8 * k + 5, 1, 5), 'E0'
    if b == 0:
        return L(8 * k + 5, 1, 2 * q + 5), 'E_b0'
    if b == 1:
        return None, 'E_exception'
    if b == 2:
        return L(8 * k + 9, q + 1), 'E_b2'
    return L(8 * k + 9, q + 2, b - 3), 'E_b3'


def as_bits(c: L) -> list[int]:
    return [1] * c.a + [0, 1] * c.q + [1] * c.b


def parse_bits(bits: list[int]) -> L | None:
    while bits and not bits[-1]:
        bits.pop()
    a = next((i for i, x in enumerate(bits) if not x), len(bits))
    if a < 2:
        return None
    if a == len(bits):
        return L(a)
    q = 0
    offset = a
    while bits[offset:offset + 2] == [0, 1]:
        q += 1
        offset += 2
    if q == 0 or not all(bits[offset:]):
        return None
    return L(a, q, len(bits) - offset)


def test_raw_macros() -> int:
    count = 0
    for k in range(4):
        for residue in range(3):
            a = 3 * k + 2 + residue
            for q in range(5):
                for b in ([0] if q == 0 else range(9)):
                    c = L(a, q, b)
                    nxt, _ = next_source_macro(c)
                    if nxt is not None:
                        _, out = physical_return(as_bits(c), 100000)
                        assert parse_bits(out) == nxt, (c, nxt, parse_bits(out))
                    count += 1
    return count


def first_exception(seed: int, budget: int = 20000) -> tuple[int, L, str]:
    c = L(seed)
    for index in range(budget):
        nxt, label = next_source_macro(c)
        if nxt is None:
            assert label == 'E_exception'
            n = c.a
            sha = hashlib.sha256(n.to_bytes((n.bit_length() + 7) // 8, 'little')).hexdigest()
            return index, c, sha
        c = nxt
    raise AssertionError(f'No E exception in first {budget} conditional macros of seed {seed}')


def main() -> None:
    checks = test_raw_macros()
    assert checks == 444
    print(f'Raw first-physical-F0 checks matching source-derived L formulas: {checks}/444')
    expected = {5: (1711, 5, 4, 2424), 9: (8394, 6, 4, 11882),
                15: (9458, 9, 4, 13388), 39: (7611, 7, 1, 10776)}
    for seed in expected:
        index, c, sha = first_exception(seed)
        facts = (index, c.q, c.a % 9, c.a.bit_length())
        assert facts == expected[seed], (seed, facts)
        print(f'CONDITIONAL seed={seed}: index={index}, q={c.q}, b={c.b}, '
              f'a_mod9={c.a % 9}, a_bits={c.a.bit_length()}, SHA256_le={sha}')


if __name__ == '__main__':
    main()
