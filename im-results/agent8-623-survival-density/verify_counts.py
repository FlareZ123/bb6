"""Exact finite counting regression for Cryptids #623's complete B-drain.

The mathematical proof is in README.md. This executable verifies small
enumerations and the all-n rational exponential envelope on a larger range.
It uses the original-source-equivalent one-level ternary recurrence established
in Agent49FlatDrainSource.lean. No external packages or file writes.
"""

from fractions import Fraction


def succeeds(a: int, b: int) -> bool:
    """Whether the source's drainB a b d returns a D, independent of d."""
    while b:
        q, r = divmod(b, 3)
        if r == 0:
            a, b = a + 1, q - 1
        elif r == 1:
            if a == 0:
                return False
            a, b = a - 1, q
        elif a == 0:
            b = q
        else:
            a, b = a - 1, q + 1
    return True


def exact_counts(max_length: int):
    """Yield (n, first-counter counts) with exact O(max_length^2) arithmetic."""
    width = 2 * max_length + 4
    previous = [1] * width
    yield 0, previous
    for n in range(1, max_length + 1):
        current = [0] * width
        current[0] = previous[0] + previous[1] + int(n % 2 == 0)
        current[1] = 2 * previous[0] + previous[2] - int(n % 2 == 1)
        for a in range(2, width - 1):
            current[a] = previous[a + 1] + 2 * previous[a - 1]
        # The high-index tail is outside the dependency cone of a <= max_length.
        current[-1] = 3**n
        yield n, current
        previous = current


def main():
    for n, counts in exact_counts(150):
        total = 3**n
        if n <= 9:
            for a in range(12):
                direct = sum(succeeds(a, b) for b in range(total))
                assert direct == counts[a], (n, a, direct, counts[a])
        for a in range(16):
            bound = 3 * Fraction(3, 2)**a * Fraction(17, 6)**n
            assert counts[a] <= bound, (n, a, counts[a], bound)
        if n in (0, 3, 6, 9, 12, 20, 50, 100, 150):
            print(
                f"n={n:3d} total={total} S0={counts[0]} S1={counts[1]} "
                f"fraction_S0={Fraction(counts[0], total)}"
            )
    print("PASS: direct source-shaped enumeration n<=9, exact recurrence n<=150, "
          "rational exponential bound for first counters 0..15.")


if __name__ == "__main__":
    main()
