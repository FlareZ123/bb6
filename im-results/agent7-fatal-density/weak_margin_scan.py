"""Deterministic experimental census of the #746 weak-margin second t=1 inverse fork.
Results are finite evidence only; never use as source/root proof.
"""
from collections import Counter
from sys import argv

def scan(max_index: int):
    stats = Counter()
    examples = []
    exceptions = []
    for n in range(13, max_index + 1):
        if n % 6 not in (4, 5):
            continue
        P = 1 << n
        k = n - 4
        p = 1 << k
        for j in range(n):
            D = (1 << j) * (2 * n + 3) - (n - 1)
            if 32 * D + 64 * n + 128 > P:
                break
            u = 4 * P - D
            if (2 * u + 5) % 9:
                continue
            d = (2 * u + 5) // 9
            h = 4 * d - 2 * P - n - 3
            w = 2 * h - 2 * P - (n - 2)
            if h % 3 != 0 or (2 * w + 5) % 9:
                continue
            stats["possible_secondary_tone"] += 1
            if (2 * w + 5) % 27 == 0:
                stats["higher_secondary_valuation"] += 1
                continue
            d2 = (2 * w + 5) // 9
            q = 4 * d2 - 8 * p - k - 5
            if not 6 * p - 1 <= q <= 8 * p - 3:
                stats["outside_even_band"] += 1
                exceptions.append((n, j, "outside band", q))
                continue
            if q % 3 == 2 or (8 * p + k) % 3 != 2:
                stats["unsafe_residue"] += 1
                exceptions.append((n, j, "unsafe residue", q))
                continue
            x = q
            steps = 0
            while 6 * p - 1 <= x <= 8 * p - 3:
                x = 2 * x - 8 * p - k
                steps += 1
            if 4 * p - 3 < x < 6 * p - 1:
                stats["gap_exit"] += 1
                stats[f"exit_depth_{steps}"] += 1
                if len(examples) < 20:
                    examples.append((n, j, steps, h, w, q, x))
            else:
                stats["other_exit"] += 1
                exceptions.append((n, j, "other exit", x))
    return stats, examples, exceptions

if __name__ == "__main__":
    maximum = int(argv[1]) if len(argv) > 1 else 3000
    counts, examples, exceptions = scan(maximum)
    print(f"n <= {maximum}")
    print(dict(sorted(counts.items())))
    print("first examples", examples)
    print("first exceptions", exceptions[:20])
