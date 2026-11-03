"""Exact arithmetic screening of the original Machine C section equations.

This is a copied-source interpreter and a finite regression, not an original
import or a proof that any machine halts or does not halt.
"""


def bounce(k: int, c: int) -> tuple[int, int] | None:
    while True:
        if c < 4:
            return None
        if k % 2:
            if c <= 2 * k + 6:
                return 2 * k + 6 - c, c
            c, k = c - (2 * k + 3), 2 * k + 3
        elif c == 4:
            return 2 * k + 2, 3
        elif c == 5:
            return None
        elif c <= 2 * k + 8:
            return 2 * k + 8 - c, c - 1
        else:
            c, k = c - (2 * k + 5), 2 * k + 4


def section(a: int, k: int) -> tuple[int, int] | None:
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


def main() -> None:
    state = (5, 1)
    hits: list[tuple[int, int]] = []
    for n in range(1, 400_001):
        state = section(*state)
        assert state is not None, ("Stopped before bounded test finished", n)
        if state[0] == 1:
            hits.append((n, state[1]))
        if n == 150_052:
            assert state == (621_619, 213_453), ("Reference divergence", n, state)
    assert hits == [(957, 3310), (24232, 84819), (397199, 1390010)]
    print("Source-equation regression succeeded through 400000 sections.")
    print("All left-one hits (section index, right counter):", hits)


if __name__ == "__main__":
    main()
