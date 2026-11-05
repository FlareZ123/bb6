"""Independent exact-integer checks of the all-index low stopping fibre formula.

The input section is a direct iterative translation of the source
BB6.Agent46.exactSection/BB6.Agent46.bounce *Option* component.
This program is finite evidence, not an all-parameter formal proof.
"""

def bounce(k: int, c: int) -> tuple[int, int] | None:
    while True:
        if c < 4:
            return None
        if k % 2:
            if c <= 2 * k + 6:
                return (2 * k + 6 - c, c)
            c -= 2 * k + 3
            k = 2 * k + 3
        else:
            if c == 4:
                return (2 * k + 2, 3)
            if c == 5:
                return None
            if c <= 2 * k + 8:
                return (2 * k + 8 - c, c - 1)
            c -= 2 * k + 5
            k = 2 * k + 4


def section(a: int, k: int) -> tuple[int, int] | None:
    if a == 0:
        if k == 0:
            return None
        if k == 1:
            return (0, 4)
        return bounce(1, 2 * k + 1)
    if a == 1:
        if k == 0:
            return (5, 1)
        if k == 1:
            return (2, 3)
        if k == 2:
            return (2, 5)
        if k == 3:
            return (0, 7)
        return bounce(4, 2 * k - 3)
    if k == 0:
        return (a - 2, 2)
    if 2 * k <= a:
        return (a - 2 * k, 2 * k + 2)
    return bounce(a - 1, 2 * k - a + 3)


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def fibre(m: int) -> tuple[int, list[tuple[int, int]]]:
    assert m >= 0
    K = (1 << (2 * m + 3)) - (3 * m + 4)
    if m % 2:
        r = v2(m + 1)
        parents = []
        for n in range(0, r - 1, 2):
            a = (K + 1) // (1 << (n + 1)) - 2
            k = (2 * K - a - 6 - 3 * n) // 2
            parents.append((a, k))
    else:
        r = v2(3 * m + 2)
        parents = [(K - 1, (K - 2) // 2)]
        for n in range(1, r - 1, 2):
            a = (K + 2) // (1 << (n + 1)) - 3
            k = (2 * K - a - 6 - 3 * n) // 2
            parents.append((a, k))
    count = r // 2 if m % 2 else 1 + (r - 1) // 2
    assert len(parents) == count
    return K, parents


def exact_inverse(x: int, y: int) -> list[tuple[int, int]]:
    """Unfiltered logarithmic source candidate equations, then exact section filter."""
    e = x + 2 * y
    cand = {(x + 2, 0), (max(x + y - 2, 0), max(y - 2, 0) // 2),
            (1, 2), (1, 3)}
    for n in range((x + y + 1).bit_length() + 1):
        scale = 1 << (n + 1)
        a0 = max((x + y) // scale - 2, 0)
        a1 = max((x + y + 1) // scale - 3, 0)
        cand.update(((0, max(e - 9 - 3 * n, 0) // 2),
                     (1, max(e - 11 - 3 * n, 0) // 2),
                     (a0, max(e - a0 - 7 - 3 * n, 0) // 2),
                     (a1, max(e - a1 - 7 - 3 * n, 0) // 2)))
    return sorted((a, k) for a, k in cand if section(a, k) == (x, y))


def main() -> None:
    for m in range(5000):
        K, parents = fibre(m)
        assert len(parents) == len(set(parents)), m
        assert all(a >= 0 and k >= 0 and section(a, k) == (1, K)
                   for a, k in parents), m
    print("PASS: 5000 predicted fibres, all parents source-valid and distinct")

    for m in range(60):
        K, parents = fibre(m)
        assert sorted(parents) == exact_inverse(1, K), m
    print("PASS: first 60 fibres coincide with exact filtered inverse enumeration")

    for m in range(1, 5000, 4):
        assert not fibre(m)[1], m
    print("PASS: every tested m = 1 mod 4 has zero immediate source predecessors")


if __name__ == "__main__":
    main()
