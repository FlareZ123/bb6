"""Exact prefix-free census of single-direction, fresh-blank drift certificates.

Only standard Python is required. Each recursive path fixes the zero-reading
transition of every state first visited from A; other table entries are free.
"""
from collections import Counter
from math import factorial


def leaf_counts() -> Counter[int]:
    counts: Counter[int] = Counter()

    def visit(path: tuple[int, ...]) -> None:
        for write in (0, 1):
            for next_state in range(6):
                if next_state in path:
                    counts[len(path)] += 1
                else:
                    visit(path + (next_state,))

    for _direction in (0, 1):
        visit((0,))
    return counts


def main() -> None:
    counts = leaf_counts()
    for length in range(1, 7):
        expected = 2 * factorial(5) // factorial(6 - length) * length * 2**length
        assert counts[length] == expected
        print(f"path length {length}: {counts[length]:,} disjoint cylinders")
    cylinders = sum(counts.values())
    represented = sum(counts[length] * 25 ** (12 - length) for length in counts)
    total = 25**12
    assert represented == 22256997070312500
    assert cylinders == 139284
    assert represented <= total
    print(f"TOTAL cylinders: {cylinders:,}")
    print(f"TOTAL full 25-choice machines covered: {represented:,}")
    print(f"FULL 25-choice universe: {total:,}")
    print(f"exact coverage fraction: {represented}/{total}")
    print(f"percentage: {100*represented/total:.9f}%")


if __name__ == '__main__':
    main()
