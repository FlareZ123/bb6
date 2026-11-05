"""Independent literal BB6CLine.nextC edge verifier for reverse384.cpp --paths.

Pass the printed path stream on stdin. This validates each abstract edge by
finding a concrete source-state representative, NOT one consistent natural run.
No synthetic abstract path proves that Machine C halts from its blank start.
"""
import sys
from itertools import product


def next_c(a, k, c):
    if c == 1:
        return a, k + 1, 0
    if c == 2:
        return None
    if c == 3:
        return a, k + 2, 1
    if c == 0:
        if a == 0:
            return 1, 0, 2 * k + 2
        if a == 1:
            return (5, 0, 1) if k == 0 else (2, 2, 2 * k - 1)
        return a - 2, 1, 2 * k + 1
    if a == 0:
        return (2 * k + 2, 2, c - 3) if k % 2 == 0 else (2 * k + 3, 0, c)
    return a - 1, k + 1, c - 1


def abstract(state):
    a, k, c = state
    return a % 384, k % 384, c if c < 2 else c % 192 + 2


def has_witness(source, target):
    a, k, cc = source
    for da, dk, dc in product(range(3), repeat=3):
        c = cc if cc < 2 else cc - 2 + 192 * dc
        if cc >= 2 and c < 2:
            continue
        result = next_c(a + 384 * da, k + 384 * dk, c)
        if result is not None and abstract(result) == target:
            return True
    return False


def main():
    paths = {}
    current = None
    for line in sys.stdin:
        text = line.strip()
        if text.startswith("PATH_BEGIN m="):
            current = int(text.removeprefix("PATH_BEGIN m="))
            paths[current] = []
        elif text.startswith("PATH_END m="):
            assert current == int(text.removeprefix("PATH_END m="))
            current = None
        elif current is not None:
            paths[current].append(tuple(map(int, text.split())))

    assert current is None
    assert set(paths) == {19, 35, 67, 83, 99, 115}
    for m, path in sorted(paths.items()):
        assert path[0] == (5, 0, 1)
        assert path[-1] == (1, (124 - 3 * m) % 384, 0)
        for i, (s, t) in enumerate(zip(path, path[1:])):
            if not has_witness(s, t):
                raise AssertionError(f"m={m}, edge={i}, source={s}, target={t}")
        print(f"m={m}: {len(path)-1} abstract transitions, all edges independently witnessed")


if __name__ == "__main__":
    main()
