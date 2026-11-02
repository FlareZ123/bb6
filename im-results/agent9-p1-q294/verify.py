"""Independent finite P1 q=294 inverse-cone audit (experimental, not Lean-certified).

Implements source-verified inverseAt arithmetic of Agent47P1, then enumerates the
two actual Agent45 n=16q+2 necessary feeder roots. Requires Python 3 stdlib.
No output files; deterministic and fully exhaustive for q294 (if completed).
"""
from collections import Counter, deque
from time import perf_counter


def inverse_at(b: int, d: int):
    """Exact source P1FiniteInverse.inverseAt recursion, stopping at first none."""
    if b < 4 or b % 4:
        return
    k, c, t = b // 4 - 1, d + b // 2, 0
    while True:
        yield t, k, c
        if c < 3 or c % 2 == 0:
            return
        v = (c - 3) // 2
        k, c, t = k + v // 2 + 1, v, t + 1


def is_14_power(n: int) -> bool:
    if n % 14:
        return False
    v = n // 14
    return v > 0 and (v & (v - 1)) == 0


def audit(q: int = 294, cap: int = 1_000_000):
    u = 7 * 2 ** (16 * q) - 4 * q - 3
    print("q", q, "critical n", 16 * q + 2, "u bits", u.bit_length())
    for i, root in enumerate(((4 * u - 4, 4 * u + 9), (6 * u - 2, 2 * u + 5))):
        pending = deque([(root[0], root[1], 0)])
        visited = set()
        leaves = Counter()
        max_cost = 0
        min_score = None
        start = perf_counter()
        while pending and len(visited) < cap:
            b, d, m = pending.popleft()
            if (b, d) in visited:
                continue
            assert b >= 8 and b % 4 == 0 and d % 2 == 1
            visited.add((b, d))
            max_cost = max(max_cost, m)
            score = b - 4 * m - 192 * q - 40
            min_score = score if min_score is None else min(score, min_score)
            if score <= 0:
                leaves["small_left_barrier_crossed"] += 1
            for t, k, c in inverse_at(b, d):
                if c == 1:
                    leaves["exceptional_c1"] += 1
                    continue
                if c == 0:
                    leaves["terminal_c0"] += 1
                    continue
                if k < 2:
                    leaves["terminal_k_lt_2"] += 1
                    continue
                x, y = 2 * k - 4, c + 4
                if c % 2 == 0:
                    if x <= 0:
                        leaves["even_x_zero"] += 1
                    elif is_14_power(x + 12):
                        leaves["even_power_hit"] += 1
                    else:
                        leaves["even_power_obstruction"] += 1
                    max_cost = max(max_cost, m + t + 1)
                elif x % 4 == 2:
                    if x <= 2:
                        leaves["odd_mod4_small"] += 1
                    else:
                        leaves["odd_mod4_obstruction"] += 1
                elif x >= 8 and x % 4 == 0:
                    pending.append((x, y, m + t + 1))
                else:
                    leaves["other_unclassified"] += 1
        print("feeder", i, "exhausted", not pending, "odd_hubs", len(visited),
              "backlog", len(pending), "max_inverse_cost", max_cost,
              "threshold_15q", 15 * q, "all_small_left_scores_positive", min_score > 0,
              "min_score_bits", min_score.bit_length(), "leaves", dict(leaves),
              "elapsed_s", round(perf_counter() - start, 2))


if __name__ == "__main__":
    audit()
