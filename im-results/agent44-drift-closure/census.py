"""Exact prefix-free censuses of directed and all-zero finite-control drift.

All machine counts use 12 independently assigned 25-choice slots. Each leaf
fixes the zero-reading transition for each state on the unique A-start orbit
up to its first repeated state; all other slots are unrestricted.
"""
from collections import Counter
from math import factorial


def leaf_counts(mode: str) -> Counter[int]:
    counts: Counter[int] = Counter()

    def visit(path: tuple[int, ...], actions: tuple[tuple[int, int], ...]) -> None:
        for _write, _direction in actions:
            for next_state in range(6):
                if next_state in path:
                    counts[len(path)] += 1
                else:
                    visit(path + (next_state,), actions)

    if mode == 'directed':
        for direction in (0, 1):
            visit((0,), ((0, direction), (1, direction)))
    elif mode == 'zero':
        visit((0,), ((0, 0), (0, 1)))
    elif mode == 'intersection':
        for direction in (0, 1):
            visit((0,), ((0, direction),))
    else:
        raise ValueError(mode)
    return counts


def main() -> None:
    counts = {kind: leaf_counts(kind) for kind in ('directed', 'zero', 'intersection')}
    union: Counter[int] = Counter()
    for k in range(1, 7):
        base = factorial(5) // factorial(6-k) * k
        assert counts['directed'][k] == 2 * base * 2**k
        assert counts['zero'][k] == base * 2**k
        assert counts['intersection'][k] == 2 * base
        union[k] = counts['directed'][k] + counts['zero'][k] - counts['intersection'][k]
        print(f'k={k}: directed {counts["directed"][k]:,}, '
              f'zero {counts["zero"][k]:,}, overlap {counts["intersection"][k]:,}, '
              f'union {union[k]:,}')

    total = 25**12
    one_halt_total = 12 * 24**11
    for name, family in (*counts.items(), ('union', union)):
        cylinders = sum(family.values())
        machines = sum(n * 25**(12-k) for k, n in family.items())
        one_halt = sum(n * (12-k) * 24**(11-k) for k, n in family.items())
        print(f'{name}: {cylinders:,} cylinders, {machines:,}/{total:,} full machines '
              f'({100*machines/total:.9f}%), '
              f'{one_halt:,}/{one_halt_total:,} exactly-one-halt machines '
              f'({100*one_halt/one_halt_total:.9f}%)')
    assert sum(n * 25**(12-k) for k, n in union.items()) == 26171093750000000
    assert sum(n * (12-k) * 24**(11-k) for k, n in union.items()) == 7226311367983104


if __name__ == '__main__':
    main()
