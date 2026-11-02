"""Exact symbolic census of sparse six-state gliders (25 canonical choices/slot)."""
from collections import Counter
from itertools import product

N = 6
Q = 25
TOTAL = Q ** (2 * N)
ONE_HALT = 2 * N * 24 ** (2 * N - 1)


def gliders():
    for d in (0, 1):
        reverse = 1 - d
        for b, c, u in product(range(1, N), range(N), range(2)):
            p = {(0, 0): (1, d, b), (b, 0): (0, reverse, c),
                 (c, 1): (u, d, 0)}
            assert len(p) == 3
            yield ("three", d, b, c, u), p
        for b, c, v, u, z in product(range(N), range(N),
                                      range(2), range(2), range(2)):
            required = [
                ((0, 0), (1, d, b)),
                ((b, 0), (v, reverse, 0)),
                ((0, 1), (u, d, c)),
                ((c, v), (z, d, 0)),
            ]
            p = {}
            for slot, move in required:
                if slot in p and p[slot] != move:
                    break
                p[slot] = move
            else:
                assert len(p) in (3, 4)
                yield ("four", d, b, c, v, u, z), p

        for b, c, v in product(range(1, N), range(N), range(2)):
            p = {(0, 0): (1, d, b), (b, 0): (v, reverse, c),
                 (c, 1): (0, reverse, 0)}
            assert len(p) == 3
            yield ("turnaround", d, b, c, v), p


def compatible(x, y):
    return all(y[s] == move for s, move in x.items() if s in y)


def main():
    items = list(gliders())
    counts = Counter(name[0] for name, _ in items)
    assert counts == {"three": 120, "four": 380, "turnaround": 120}, counts
    for i, (name, table) in enumerate(items):
        assert table[(0, 0)][0] == 1
        b = table[(0, 0)][2]
        assert table[(b, 0)][1] != table[(0, 0)][1]
        for previous, other in items[:i]:
            assert not compatible(table, other), (name, previous)
    total = sum(Q ** (2 * N - len(p)) for _, p in items)
    one_halt = sum((2 * N - len(p)) * 24 ** (2 * N - len(p) - 1)
                   for _, p in items)
    assert total == 1_046_752_929_687_500
    assert one_halt == 270_785_272_872_960
    previous_total = 26_171_093_750_000_000
    previous_one = 7_226_311_367_983_104
    print(f"cylinders by type: {dict(counts)}; pairwise overlaps: 0")
    print(f"all canonical tables: {total}/{TOTAL} = {100*total/TOTAL:.8f}%")
    print(f"exactly-one-halt tables: {one_halt}/{ONE_HALT} = {100*one_halt/ONE_HALT:.8f}%")
    print("Every glider writes 1 in A/0, excluding zero-writer closure.")
    print("Every glider has A/0 direction opposite B/0, excluding directed drift closure.")
    print(f"union with Agent44: {(previous_total+total)/TOTAL*100:.8f}% all tables")
    print(f"union with Agent44: {(previous_one+one_halt)/ONE_HALT*100:.8f}% one-halt tables")


if __name__ == "__main__":
    main()
