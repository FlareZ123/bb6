"""Reproduce the bounded empirical coverage comparison for Machine C.

This file is supplementary experimental code, not a soundness proof.
The formal kernel-checked proof is in MixedFourNormalize.lean and
MixedFourFilter.lean. The high stopping equation is in SectionParam.lean.

Sweep m=1..31 and j=0..511, compare the old three-gate inverse
normalizer to the new mixed four-gate normalizer. No file outputs.
"""

from collections import Counter


def normalize(x: int, y: int, include_six_even: bool) -> tuple[int, int, int]:
    steps = 0
    while True:
        total = x + y
        old_rank = x + 2 * y

        if x % 2 == 1 and y % 2 == 1 and y >= 5 and total % 4 == 0 and total % 16 != 0 and total >= 24:
            x, y = (total - 4) // 2, (x + 3 * y - 10) // 4
        elif x % 2 == 0 and y % 2 == 1 and y >= 5 and (total + 1) % 16 == 8 and total >= 23:
            x, y = (total - 5) // 2, (x + 3 * y - 9) // 4
        elif y >= 4 and y % 2 == 0 and total % 4 == 1:
            x, y = total - 2, (y - 2) // 2
        elif include_six_even and y >= 6 and y % 2 == 0 and total % 8 not in (0, 7):
            x, y = total - 2, (y - 2) // 2
        else:
            return x, y, steps

        assert x + 2 * y < old_rank, (x, y, old_rank)
        steps += 1


def forbidden_odd_image(result: tuple[int, int, int]) -> bool:
    x, y, _steps = result
    return y >= 5 and y % 2 == 1 and (x + y) % 4 in (1, 2)


def census() -> None:
    stats = Counter()
    first_extra = None

    for m in range(1, 32):
        factor = 1 << (2 * m + 2)

        for j in range(512):
            x = 2 * j + 3
            k = factor * (j + 3) - j - 3 * m - 5
            assert k >= 0
            assert k + j + 3 * m + 5 == factor * (j + 3)

            old = forbidden_odd_image(normalize(x, k, include_six_even=False))
            mixed = forbidden_odd_image(normalize(x, k, include_six_even=True))

            stats[(m, "old")] += int(old)
            stats[(m, "mixed")] += int(mixed)
            if mixed and not old and first_extra is None:
                first_extra = (m, j, x, k)

    old_total = sum(stats[(m, "old")] for m in range(1, 32))
    mixed_total = sum(stats[(m, "mixed")] for m in range(1, 32))

    print(f"examined: {31 * 512}")
    print(f"old three-gate exclusions: {old_total}")
    print(f"new four-gate exclusions: {mixed_total}")
    print(f"additional exclusions: {mixed_total - old_total}")
    print(f"first new target (m,j,x,k): {first_extra}")
    print("per-m: m old mixed extra")
    for m in range(1, 32):
        old = stats[(m, "old")]
        new = stats[(m, "mixed")]
        print(m, old, new, new - old)

    assert (old_total, mixed_total, mixed_total - old_total) == (6015, 8488, 2473)
    assert first_extra is not None


if __name__ == "__main__":
    census()
