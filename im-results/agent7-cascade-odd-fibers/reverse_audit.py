"""Independent inverse-image falsification probe for #746 fatal n mod6=0..3.

Derived from source-indexed reset map: even outputs at scale 2^m fill
[6*2^m-1, 8*2^m-3] with inverse h=2*t-8*2^m-m;
odd outputs are 2 mod3. A residual outside all even intervals and not
2 mod3 has no reset predecessor. This is finite experimental evidence,
not a proof of the all-index exclusion or of blank-tape nonhalting.
"""
from __future__ import annotations

import hashlib


def inverse_even(t: int) -> int | None:
    m = max(0, ((t + 1) // 6).bit_length() - 1)
    p = 1 << m
    if 6 * p - 1 <= t <= 8 * p - 3:
        return 2 * t - 8 * p - m
    return None


def check(N: int = 2048) -> None:
    digest = hashlib.sha256()
    checked = total_edges = max_depth = 0
    for n in range(N + 1):
        if n % 6 not in (0, 1, 2, 3):
            continue
        x = (4 << n) - n - 4
        depth = 0
        while True:
            assert x % 3 != 2, (n, depth, "odd-exit possible", x)
            pred = inverse_even(x)
            if pred is None:
                assert x != 2, (n, depth, "root collision")
                break
            assert 0 <= pred < x, (n, depth, "invalid inverse", x, pred)
            x = pred
            depth += 1
        checked += 1
        total_edges += depth
        max_depth = max(max_depth, depth)
        digest.update(f"{n}:{depth}:{x}\n".encode())
    print(f"PASS: n<= {N}; {checked} excluded-index reverse audits; "
          f"{total_edges} exact even inverse edges; max depth {max_depth}; "
          "every chain exits in a gap before odd output or blank root")
    print("SHA256 terminal transcript:", digest.hexdigest())


if __name__ == "__main__":
    check()
