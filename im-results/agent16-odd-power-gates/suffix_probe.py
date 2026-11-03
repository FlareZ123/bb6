"""Falsify finite low-bit suffix shields on the genuine Sheep blank-even orbit."""

from __future__ import annotations

from collections import defaultdict


def section(t: int) -> int:
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        raise RuntimeError("Reached an authentic halting power")
    return t + a + (3 if u == 3 else (u - 1) // 2)


def even_return(t: int) -> int:
    z = section(t)
    q = z - 1
    h = (q & -q).bit_length() - 1
    return 1 + 3**h * (q >> h)


def main() -> None:
    horizon = 30_000
    lengths = range(7, 31)
    # The modulus-specific suffix is fixed after the witness word exceeds 30 bits.
    source = 2 * ((2**84 - 1) // 5)
    suffix = {bits: source % (1 << bits) for bits in lengths}
    first: dict[int, tuple[int, int]] = {}
    counts: dict[int, int] = defaultdict(int)
    x = 10
    for index in range(horizon):
        for bits in lengths:
            if x.bit_length() >= bits and x % (1 << bits) == suffix[bits]:
                counts[bits] += 1
                first.setdefault(bits, (index, x.bit_length()))
        x = even_return(x)

    expected_first = {
        7: 357, 8: 357, 9: 547, 10: 645, 11: 645, 12: 1602,
        13: 2143, 14: 3624, 15: 6908, 16: 6908, 17: 6908, 18: 6908,
    }
    assert {bits: data[0] for bits, data in first.items()} == expected_first
    assert x.bit_length() == 23866
    print("PASS authentic blank orbit, 30000 even returns, endpoint 23866 bits")
    for bits in lengths:
        print(
            bits, format(suffix[bits], f"0{bits}b"),
            "first", first.get(bits),
            "count", counts[bits],
        )


if __name__ == "__main__":
    main()
