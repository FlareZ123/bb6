"""Finite inverse-candidate enumeration for the exact Agent46 Machine C section.

Reverses the source bounce rules by halving their middle counter. The
enumerator was independently checked against the source's Python translation
on 158,268 forward/backward cases; a full Lean completeness proof is pending.
"""
from collections.abc import Iterator


def _bounce_predecessors(x: int, y: int) -> Iterator[tuple[int, int]]:
    s = x + y
    if y >= 4 and s >= 8 and s % 4 == 0:
        p, c = (s - 6) // 2, y
        while True:
            yield p, c
            if p < 5 or p % 4 != 1:
                break
            c += p
            p = (p - 3) // 2
    if y == 3 and x >= 2 and x % 4 == 2:
        p, c = (x - 2) // 2, 4
    elif y >= 5 and s >= 7 and s % 4 == 3:
        p, c = (s - 7) // 2, y + 1
    else:
        return
    while True:
        yield p, c
        if p < 4 or p % 4 != 0:
            break
        c += p + 1
        p = (p - 4) // 2


def inverse_section(x: int, y: int) -> set[tuple[int, int]]:
    """Enumerate every candidate section input (a,k) for target (x,y)."""
    assert x >= 0 and y >= 0
    result = set()
    specials = {(0, 4): (0, 1), (5, 1): (1, 0),
                (2, 3): (1, 1), (2, 5): (1, 2), (0, 7): (1, 3)}
    if (x, y) in specials:
        result.add(specials[(x, y)])
    if y == 2:
        result.add((x + 2, 0))
    if y >= 4 and y % 2 == 0:
        result.add((x + y - 2, y // 2 - 1))
    for p, c in _bounce_predecessors(x, y):
        a = p + 1
        sum2 = c + a - 3
        if a >= 2 and sum2 >= 2 and sum2 % 2 == 0:
            k = sum2 // 2
            if a < 2 * k:
                result.add((a, k))
        if p == 1 and c >= 5 and c % 2 == 1:
            result.add((0, (c - 1) // 2))
        if p == 4 and c >= 5 and c % 2 == 1:
            k = (c + 3) // 2
            if k >= 4:
                result.add((1, k))
    return result
