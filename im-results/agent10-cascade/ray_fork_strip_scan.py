"""Deterministic numerical audit for the source-proved #746 ray fork strip.

The Lean theorems, not this script, justify nonreachability. This program
counts exact algebraic t=1 odd-reset predecessor candidates that satisfy
those theorems' hypotheses. No finite census settles all fatal indices.
"""
from collections import Counter
from hashlib import sha256


def scan(last_n: int = 600) -> None:
    counts: Counter[tuple[int, bool, bool]] = Counter()
    digest = sha256()
    eligible = 0

    for n in range(13, last_n + 1):
        if n % 6 not in (4, 5):
            continue
        power = 1 << n
        deficit = n + 4
        j = 0
        while 32 * deficit + 64 * n + 128 <= power:
            ray = 4 * power - deficit
            numerator = 2 * ray + 5
            if numerator % 9 == 0:
                d = numerator // 9
                q = 2 * d
                k = n - 2
                scale = 1 << k
                if 6 * scale + 1 <= q <= 8 * scale - 1:
                    h = 4 * d - 8 * scale - k - 5
                    w = 2 * h - 2 * power - k
                    assert d % 2 == 1
                    assert h >= 0 and w >= 0
                    assert 9 * h + 8 * deficit + 9 * n + 7 == 14 * power
                    assert 2 * h == 2 * power + w + k
                    assert power < w and 8 * w + 32 < 9 * power
                    cat = (h % 3, (2 * h + 5) % 27 == 0,
                           (2 * w + 5) % 9 == 0)
                    counts[cat] += 1
                    digest.update(
                        f"{n},{j},{h % 3},{(2*h+5)%27},{(2*w+5)%9}\n".encode()
                    )
                    eligible += 1
            deficit = 2 * deficit + n - 1
            j += 1

    proved = sum(
        count for (hmod, h27, w9), count in counts.items()
        if not h27 and (hmod != 0 or not w9)
    )
    print(f"n=13..{last_n}, sectors 4/5 mod 6")
    print(f"Exact high-margin t=1 candidate pairs (n,j): {eligible}")
    print(f"Covered by source-checked universal theorems: {proved}")
    print(f"Not yet covered by these theorems: {eligible-proved}")
    for label in sorted(counts):
        print(f"  hmod3={label[0]}, h27div={label[1]}, w9div={label[2]}: {counts[label]}")
    print(f"Rows SHA256: {digest.hexdigest()}")


if __name__ == "__main__":
    scan()
