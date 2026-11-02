"""Exact integer inverse of the published Space Needle one-counter map.

The equivalence is formally verified in SpaceNeedleClosed.lean:
  highLevelNext_iff_oddTower and predecessor_power_identity.
"""


def high_level_next(d: int) -> int | None:
    """One certified high-level return on a nonnegative natural counter."""
    x = d + 2
    v = (x & -x).bit_length() - 1
    odd_part = x >> v
    if odd_part == 1:
        return None
    return d + v + 3 * ((odd_part - 1) // 2)


def predecessors(y: int) -> tuple[int, ...]:
    """All natural input counters that lead to y in one high-level step.

    Invert 2y+7 = (2^(v+1)+3)*odd_part + 2v, odd_part >= 3.
    Every predecessor is strictly smaller than y, and v<bit_length(y).
    """
    out = []
    for v in range(y.bit_length()):
        denominator = (1 << (v + 1)) + 3
        numerator = 2 * y + 7 - 2 * v
        if numerator < 3 * denominator:
            break
        odd_part, remainder = divmod(numerator, denominator)
        if remainder == 0 and odd_part % 2 == 1:
            d = (odd_part << v) - 2
            assert 0 <= d < y
            assert high_level_next(d) == y
            out.append(d)
    return tuple(out)


def reverse_cone(terminal: int) -> frozenset[int]:
    """Exhaustive finite predecessor closure of a positive terminal target."""
    seen = {terminal}
    stack = [terminal]
    while stack:
        for source in predecessors(stack.pop()):
            if source not in seen:
                seen.add(source)
                stack.append(source)
    return frozenset(seen)
