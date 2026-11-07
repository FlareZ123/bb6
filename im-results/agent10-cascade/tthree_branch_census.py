"""Finite census of genuine source-C algebraic t=3 candidates for #746.

No claim is made about actual root reachability or BB(6). The output
partitions candidates by precise modular gates proved in Lean.
"""
from collections import Counter
from hashlib import sha256


def census(max_index: int = 1500) -> tuple[Counter[str], str]:
    counts: Counter[str] = Counter()
    digest = sha256()
    for n in range(20, max_index + 1):
        if n % 6 not in (4, 5):
            continue
        power = 1 << n
        deficit = n + 4
        depth = 0
        while 2048 * deficit + 16384 * n + 16384 <= power:
            ray = 4 * power - deficit
            numerator = 2 * ray + 5
            if numerator % 81 == 0:
                quotient = numerator // 81
                image = 8 * quotient
                scale = 1 << (n - 3)
                if 6 * scale + 1 <= image <= 8 * scale - 1:
                    parent = 16 * quotient - power - n - 2
                    digest.update(f"{n}:{depth}:{parent}\n".encode())
                    counts["all_t3_candidates"] += 1
                    if parent % 3 != 2:
                        counts["excluded_by_initial_mod3_gap"] += 1
                    else:
                        z = 2 * parent + 5
                        first_odd_quotient = z // 3
                        first_parent = (
                            2 * first_odd_quotient
                            - 8 * (1 << (n - 4))
                            - (n - 4)
                            - 5
                        )
                        if z % 9 != 0:
                            counts["excluded_by_low_q_valuation"] += 1
                        elif z % 81 != 0 and (2 * first_parent + 5) % 9 != 0:
                            counts["excluded_by_two_gate"] += 1
                        else:
                            counts["remaining_two_gate_candidates"] += 1
                            if z % 81 == 0:
                                counts["remaining_q_81_multiple"] += 1
                            if (2 * first_parent + 5) % 9 == 0:
                                counts["remaining_first_parent_9_multiple"] += 1
            depth += 1
            deficit = 2 * deficit + n - 1
    return counts, digest.hexdigest()


if __name__ == "__main__":
    result, result_sha256 = census()
    print("strong margin, n<=1500, n%6 in {4,5}")
    for key in sorted(result):
        print(f"{key}: {result[key]}")
    print("sha256 sorted candidate rows n:depth:parent:", result_sha256)
