"""Reproduce the finite A6/F287 3-root normalization census.

This is a reproducible computational audit, independent of the Lean source
proofs. It is not a Lean-checked all-pairs cardinality certificate.
"""
from hashlib import sha256
from itertools import permutations, product

SOURCE = "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---"
ROOTS = (0, 3, 4)
STATES = tuple(range(6))
ACTIONS = (None,) + tuple(
    (int(write), direction, state)
    for state, write, direction in product(STATES, "01", "LR")
)


def parse(rle):
    rows = rle.split("_")
    assert len(rows) == 6 and all(len(row) == 6 for row in rows)
    result = []
    for row in rows:
        for index in (0, 3):
            tok = row[index:index + 3]
            if tok == "---":
                result.append(None)
            else:
                assert tok[0] in "01" and tok[1] in "LR" and tok[2] in "ABCDEF"
                result.append((int(tok[0]), tok[1], ord(tok[2]) - ord("A")))
    return tuple(result)


def encode(table):
    def action(t):
        return "---" if t is None else f"{t[0]}{t[1]}{chr(65 + t[2])}"
    return "_".join(
        "".join(action(table[2 * q + b]) for b in (0, 1))
        for q in STATES
    )


def permute_root(source, old_root, rest, mirror):
    forward = dict(zip((q for q in STATES if q != old_root), rest))
    forward[old_root] = 0
    backward = {new: old for old, new in forward.items()}
    transformed = []
    for q, bit in product(STATES, (0, 1)):
        old = source[2 * backward[q] + bit]
        if old is None:
            transformed.append(None)
        else:
            write, direction, nxt = old
            new_dir = ("L" if direction == "R" else "R") if mirror else direction
            transformed.append((write, new_dir, forward[nxt]))
    return tuple(transformed)


def main():
    source = parse(SOURCE)
    assert source[11] is None and sum(a is None for a in source) == 1
    assert len(ACTIONS) == 25 and len(set(ACTIONS)) == 25

    cylinders = [
        permute_root(source, root, rest, mirror)
        for root in ROOTS
        for rest in permutations(range(1, 6))
        for mirror in (False, True)
    ]
    assert len(cylinders) == 720
    assert all(sum(t is None for t in table) == 1 for table in cylinders)
    assert all(table[2 * q] is not None for table in cylinders for q in STATES)

    # A0, B0, C0 and D0 are assigned in every cylinder.
    # Their four-action signature is sufficient to distinguish all 720.
    signatures = [tuple(table[2 * q] for q in range(4)) for table in cylinders]
    assert len(set(signatures)) == len(cylinders) == 720

    # Enumerate all complete extensions, including the retained halting action.
    completed = set()
    for table in cylinders:
        hole = table.index(None)
        for action in ACTIONS:
            full = list(table)
            full[hole] = action
            completed.add(encode(full))
    assert len(completed) == 720 * 25 == 18000

    payload = "\n".join(sorted(completed)).encode("ascii") + b"\n"
    print("source:", SOURCE)
    print("A/D/E rooted source machines:", len(ROOTS))
    print("A-fixed permutations per root:", 120)
    print("mirrors per permutation:", 2)
    print("individual certified-cylinder specifications:", len(cylinders))
    print("pairwise distinct four-slot assigned signatures:", len(set(signatures)))
    print("complete distinct six-state raw transition tables:", len(completed))
    print("sha256 sorted newline-terminated full-table RLE:", sha256(payload).hexdigest())


if __name__ == "__main__":
    main()
