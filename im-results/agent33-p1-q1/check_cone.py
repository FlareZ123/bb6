"""Exact finite P1 n=18 source inverse-cone census; no halting inference without imported Lean soundness."""
from collections import Counter

P = 2**16
U = 7 * P - 7
ROOTS = ((4 * U - 4, 4 * U + 9), (6 * U - 2, 2 * U + 5))


def inverse_at(b: int, d: int):
    assert b >= 8 and b % 4 == 0 and d % 2 == 1
    t, k, c = 0, b // 4 - 1, d + b // 2
    while True:
        yield t, k, c
        if c < 3 or c % 2 == 0:
            break
        v = (c - 3) // 2
        t, k, c = t + 1, k + v // 2 + 1, v


def check(root: tuple[int, int]):
    todo = [(root, 0)]
    visited = set()
    categories = Counter()
    min_power = 14 * 2**18
    max_power = 0
    max_depth = 0
    while todo:
        (b, d), depth = todo.pop()
        assert (b, d) not in visited, f"cycle or duplicate: {(b, d)}"
        visited.add((b, d))
        max_depth = max(max_depth, depth)
        for t, k, c in inverse_at(b, d):
            assert k >= 2 and c != 1
            x, y = 2 * k - 4, c + 4
            assert x >= 4
            if x % 4 == 2:
                categories["mod4"] += 1
                continue
            assert x % 4 == 0
            if y % 2 == 0:
                assert 28 * P < x + 12 < 56 * P
                categories["power_gap"] += 1
                min_power = min(min_power, x + 12)
                max_power = max(max_power, x + 12)
                continue
            assert x >= 8 and y % 2 == 1
            categories["odd_child"] += 1
            todo.append(((x, y), depth + 1))
    assert categories["odd_child"] + 1 == len(visited)
    return len(visited), categories, max_depth, (min_power, max_power)


if __name__ == "__main__":
    assert ROOTS == ((1834976, 1834989), (2752468, 917495))
    for i, root in enumerate(ROOTS):
        n, counts, depth, (lo, hi) = check(root)
        print(f"L{i}: root={root}, hubs={n}, edges={dict(counts)}, max_depth={depth}, even_x+12_range=[{lo},{hi}]")
    assert check(ROOTS[0])[0] == 24
    assert check(ROOTS[1])[0] == 26
    print("FINITE SOURCE-ARITHMETIC CENSUS PASSED; genuine blank reachability requires source-connected Lean audit")
