"""Exact integer cross-check of the #623 third ninefold ternary drain identity."""
from itertools import product


def drain(a: int, b: int, d: int) -> tuple[int, int] | None:
    while b:
        q, r = divmod(b, 3)
        if r == 0:
            a, b, d = a + 1, q - 1, d + 6 * q + 3
        elif r == 1:
            if a == 0:
                return None
            a, b, d = a - 1, q, d + 6 * q + 7
        elif a:
            a, b, d = a - 1, q + 1, d + 6 * q + 5
        else:
            b, d = q, d + 6 * q + 7
    return a, d


def encode(word: tuple[int, ...]) -> tuple[int, int]:
    block, charge = 6, 4
    for digit in reversed(word):
        block = 9 * block + digit
        charge += 4 if digit == 6 else 2
    return block, charge


def main() -> None:
    checked = 0
    for a in range(30):
        for b in range(300):
            for d in (0, 7):
                assert drain(a, 9 * b + 8, d) == drain(a, b, d + 24 * b + 26)
                checked += 1
    print(f"Residue-eight exact identities: {checked:,}")

    checked = 0
    for n in range(8):
        codes = set()
        for word in product((0, 6, 8), repeat=n):
            block, charge = encode(word)
            assert block > 0 and block % 2 == 0
            assert block not in codes
            codes.add(block)
            for a, d in ((0, 0), (0, 17), (2, 5), (7, 0)):
                assert drain(a, block, d) == (a, d + 3 * block + charge)
                checked += 1
        assert len(codes) == 3**n
        print(f"Length {n}: {len(codes):,} distinct successful blocks")
    print(f"Family exact outputs: {checked:,}")


if __name__ == "__main__":
    main()
