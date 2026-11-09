"""Independent integer-grammar regression for the P1 cost-level feeder pairing.

The evaluator reads only the original source-derived scalar inverse equation.
It deliberately does not use binary markers, complement formulas or odd-slope
cylinders to generate the counts. Run with Python 3; no dependencies.
"""
from collections import Counter
from functools import lru_cache
from fractions import Fraction


def count_paths(side: int, cost: int, q: int) -> int:
    L = 16 * q + side
    z0 = (12 if side == 8 else 10) * q + 4

    @lru_cache(maxsize=None)
    def count_at(m: int, z: int) -> int:
        if m == cost:
            return 1

        total = 0
        for k in range(1, cost - m + 1):
            t = k - 1
            if z % (1 << t):
                continue
            numerator = L + m + t + z // (1 << t)
            if numerator % 2 == 1:
                total += count_at(m + k, (numerator - 1) // 2)
        return total

    return count_at(0, z0)


def regression(max_cost: int = 12) -> None:
    for M in range(2, max_cost + 1):
        P = 1 << (M - 2)
        offset = (P // 2) if M % 2 else 0

        left = [count_paths(8, M, q) for q in range(P)]
        right = [count_paths(9, M - 1, q) for q in range(P)]
        assert sum(left) == sum(right) == P
        assert all(left[q] == right[(q + offset) % P] for q in range(P))

        for q in (P, P + 1, P + 7, 10 * P + 5, 1000 * P + 123):
            assert count_paths(8, M, q) == count_paths(9, M - 1, q + offset)

        second = Fraction(sum(v * v for v in left), P)
        frequencies = Counter(left)
        assert frequencies == Counter(right)
        print(
            f"cost={M:2} period={P:5} offset={offset:5} "
            f"support={sum(v > 0 for v in left):5} "
            f"maximum={max(left):3} second_moment={second} "
            f"extra_noncanonical_parameters=5"
        )


if __name__ == "__main__":
    regression()
