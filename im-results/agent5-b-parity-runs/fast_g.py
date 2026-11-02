"""Exact finite-block acceleration for the two-branch Busy Beaver B scalar map.

The Lean theorem `G_block_split` proves the identity applied at each block.
"""

from functools import lru_cache
from hashlib import sha256
from random import Random
from time import perf_counter


def g(z: int) -> int:
    return 3 * (z // 2) + 4 + 5 * (z % 2)


@lru_cache(maxsize=8)
def table(width: int) -> tuple[int, ...]:
    values: list[int] = []
    for initial in range(1 << width):
        z = initial
        for _ in range(width):
            z = g(z)
        values.append(z)
    return tuple(values)


def fast_iterate(z: int, n: int, width: int = 12) -> int:
    values = table(width)
    mask = (1 << width) - 1
    multiplier = 3**width
    for _ in range(n // width):
        z = multiplier * (z >> width) + values[z & mask]
    for _ in range(n % width):
        z = g(z)
    return z


def verify() -> None:
    rng = Random(0xBB6005)
    for _ in range(5000):
        initial = rng.randrange(1 << 45)
        n = rng.randrange(121)
        baseline = initial
        for _ in range(n):
            baseline = g(baseline)
        width = rng.randrange(1, 13)
        actual = fast_iterate(initial, n, width)
        assert actual == baseline, (initial, n, width)
    print("PASS: 5000 seeded small exact-iteration comparisons")

    t0 = perf_counter()
    z = fast_iterate(0, 227097)
    elapsed = perf_counter() - t0
    data = z.to_bytes((z.bit_length() + 7) // 8, "big")
    digest = sha256(data).hexdigest()
    assert z.bit_length() == 132847 and z % 2 == 1
    assert digest == "15d1bf0d327f41d76b4a47e6d5293cab98143a69ae12c70487be42a23f3593cc"
    print(f"PASS: n=227097, parity={z%2}, bits={z.bit_length()}, sha256={digest}")
    print(f"Block width=12, elapsed iteration time={elapsed:.3f}s")


if __name__ == "__main__":
    verify()
