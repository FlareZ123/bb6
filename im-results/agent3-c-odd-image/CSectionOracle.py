"""Independent plain-Python transcription of Agent46 source section.

For finite experimental cross-checking only. Original Lean remains the
authoritative exact source; no semantic theorem is claimed for this copy.
"""


def bounce(k: int, c: int) -> tuple[int, int] | None:
    if c < 4:
        return None
    while True:
        if k % 2:
            if c <= 2 * k + 6:
                return 2 * k + 6 - c, c
            old_k = k
            k, c = 2 * k + 3, c - (2 * old_k + 3)
        else:
            if c == 4:
                return 2 * k + 2, 3
            if c == 5:
                return None
            if c <= 2 * k + 8:
                return 2 * k + 8 - c, c - 1
            old_k = k
            k, c = 2 * k + 4, c - (2 * old_k + 5)


def sec(a: int, k: int) -> tuple[int, int] | None:
    if a == 0:
        if k == 0:
            return None
        if k == 1:
            return 0, 4
        return bounce(1, 2 * k + 1)
    if a == 1:
        if k == 0:
            return 5, 1
        if k == 1:
            return 2, 3
        if k == 2:
            return 2, 5
        if k == 3:
            return 0, 7
        return bounce(4, 2 * k - 3)
    if k == 0:
        return a - 2, 2
    if 2 * k <= a:
        return a - 2 * k, 2 * k + 2
    return bounce(a - 1, 2 * k - a + 3)
