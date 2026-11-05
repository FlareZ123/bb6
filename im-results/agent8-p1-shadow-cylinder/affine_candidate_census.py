"""Enumerate conservative affine P1 shadow certificates.

This is an exact-integer discovery tool, not a Turing-machine halting proof.
The finite graph and every required source/Reach obligation must be audited
separately in Lean before asserting blank-origin critical exclusions.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Cone:
    nodes: tuple[tuple[int, int, int], ...]
    edges: int
    max_cost: int


def v2(value: int) -> int:
    """Return the 2-adic valuation of a strictly positive integer."""
    return (value & -value).bit_length() - 1


def affine_cone(q: int, period: int, side: int) -> Cone | None:
    """Check all r >= 0 for q + period*r, with integer affine offsets."""
    assert q >= 29 and period > 0 and side in (0, 1)
    left_shift = 16 * period
    base_l = 16 * q + 8 + side
    z_base = (12 if side == 0 else 10) * q + 4
    z_slope = (12 if side == 0 else 10) * period
    pending = [(0, z_base, z_slope)]
    seen: dict[tuple[int, int], int] = {}
    edge_count = 0

    while pending:
        m, z, slope = pending.pop()
        if z <= 0 or m > 10 or z % 256 == 0 :
            return None
        key = (m, z)
        if key in seen:
            if seen[key] != slope:
                return None
            continue
        seen[key] = slope
        if len(seen) > 10000:
            return None
        depth = v2(z)
        if depth > 7 or slope % (2 ** (depth + 1)) != 0:
            return None

        for t in range(depth + 1):
            zquot = z // (2 ** t)
            slope_quot = slope // (2 ** t)
            numerator = base_l + m + t - 1 + zquot
            num_slope = left_shift + slope_quot
            if num_slope % 2 != 0:
                return None
            if numerator % 2 == 0:
                edge_count += 1
                pending.append((m + t + 1, numerator // 2, num_slope // 2))
    nodes = tuple(sorted((m, z, slope) for (m, z), slope in seen.items()))
    return Cone(nodes, edge_count, max(m for m, _, _ in nodes))


def census() -> None:
    by_period: dict[int, list[int]] = {256: [], 1024: []}
    for q in range(29, 1024):
        if q % 4 not in (1, 2):
            continue
        for period in (256, 1024):
            a = affine_cone(q, period, 0)
            b = affine_cone(q, period, 1)
            if a is not None and b is not None:
                by_period[period].append(q)
                break
    k8 = sorted({q % 256 for q in by_period[256]})
    print(f"Period 256: {len(by_period[256])} checked seeds, {len(k8)} distinct residue classes")
    print("q mod 256:", ", ".join(map(str, k8)))
    print(f"Additional period-1024-only seeds: {len(by_period[1024])}")
    print("q mod 1024:", ", ".join(map(str, by_period[1024])))
    print(f"Total q=29..1023 seeds with both cones certified by these integer conditions: "
          f"{sum(map(len, by_period.values()))}")


if __name__ == "__main__":
    census()
