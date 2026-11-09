"""Finite reproducible diagnostic for the exact six-sector Machine C inverse.

The Lean proof of the six-sector source equivalence is SixForcedNormalize.lean.
This script measures the effect of adding the even/odd valuation-two gate on
m=0 high stopping targets. Counts are finite experimental data, not a proof
that any unsampled target is unreachable.
"""
from __future__ import annotations


def inverse_step(x: int, y: int, include_evenodd_val2: bool) -> tuple[int, int] | None:
    s = x + y
    if x % 2 == 1 and y % 2 == 1 and y >= 5 and s % 4 == 0 and s % 16 != 0 and s >= 24:
        return (s - 4) // 2, (x + 3 * y - 10) // 4
    if x % 2 == 0 and y % 2 == 1 and y >= 5 and (s + 1) % 16 == 8 and s >= 23:
        return (s - 5) // 2, (x + 3 * y - 9) // 4
    if y >= 4 and y % 2 == 0 and s % 4 == 1:
        return s - 2, (y - 2) // 2
    if y >= 6 and y % 2 == 0 and s % 8 not in (0, 7):
        return s - 2, (y - 2) // 2
    if x % 16 == 5 and y % 16 == 10 and (s + 1) % 256 == 192:
        return s - 2, (y - 2) // 2
    if include_evenodd_val2 and x % 2 == 0 and y % 2 == 1 and y >= 5 and (s + 1) % 8 == 4:
        return (s - 5) // 2, (x + 3 * y - 9) // 4
    return None


def normalize(x: int, y: int, include_evenodd_val2: bool) -> tuple[int, int]:
    while (parent := inverse_step(x, y, include_evenodd_val2)) is not None:
        px, py = parent
        assert px + 2 * py < x + 2 * y
        x, y = px, py
    return x, y


def parity_excluded(x: int, y: int) -> bool:
    return y >= 5 and y % 2 == 1 and (x + y) % 4 in (1, 2)


def main() -> None:
    for n in (64, 256, 1024, 8192):
        old = newer = 0
        newly_rejected: list[int] = []
        for t in range(n):
            j = 7 + 32 * t
            x, y = 2 * j + 3, 3 * j + 7
            old_reject = parity_excluded(*normalize(x, y, False))
            new_reject = parity_excluded(*normalize(x, y, True))
            assert not old_reject or new_reject
            old += old_reject
            newer += new_reject
            if new_reject and not old_reject and len(newly_rejected) < 32:
                newly_rejected.append(t)
        print(f"t=0..{n-1}: original-five={old}, extended-six={newer}, additional={newer-old}")
        print(f"  first 32 newly rejected indices: {newly_rejected}")
        if n == 8192:
            assert (old, newer) == (2228, 2674)


if __name__ == "__main__":
    main()
