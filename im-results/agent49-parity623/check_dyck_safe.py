"""Independent exact integer check of coloured Dyck drains for BB(6) #623."""
from itertools import product
from math import comb

from check_third_ninefold import drain


def dyck_shapes(n, ups=0, downs=0, word=()):
    if downs == n:
        yield word
    if ups < n:
        yield from dyck_shapes(n, ups + 1, downs, word + ("u",))
    if downs < ups:
        yield from dyck_shapes(n, ups, downs + 1, word + ("d",))


def block_charge(word):
    block, charge = 6, 4
    for step in reversed(word):
        if step == 0:
            block = 3 * (block + 1)
        elif step == 1:
            block = 3 * block + 1
            charge += 4
        else:
            block = 3 * block - 1
            charge += 2
    return block, charge


def main():
    for n in range(8):
        blocks = set()
        for shape in dyck_shapes(n):
            for colours in product((1, 2), repeat=n):
                downs = iter(colours)
                word = tuple(0 if step == "u" else next(downs) for step in shape)
                block, charge = block_charge(word)
                assert block not in blocks
                blocks.add(block)
                for a, d in ((0, 0), (1, 7), (7, 13)):
                    assert drain(a, block, d) == (a, d + 3 * block + charge)
        expected = (1 << n) * comb(2 * n, n) // (n + 1)
        assert len(blocks) == expected
        print(f"n={n}: {len(blocks):,} unique source-exact outputs, max block={max(blocks):,}")


if __name__ == "__main__":
    main()
