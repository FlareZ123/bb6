#!/usr/bin/env python3
"""Independent finite raw-vs-P1 audit; never interpret a prefix as nonhalting.

Machine RLE and equations from pinned Cryptids commit:
ced8f9f44f67a167d5ecc03e687b048c67926371
"""
from collections import Counter

RLE = "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"
MAX_A, MAX_C, RAW_FUEL, BLANK_MACRO_STEPS = 39, 39, 100_000, 100


def parse_rle(rle):
    rows = rle.split("_")
    assert len(rows) == 6 and all(len(row) == 6 for row in rows)
    table = {}
    for i, row in enumerate(rows):
        for symbol in (0, 1):
            triple = row[3 * symbol:3 * symbol + 3]
            assert triple == "---" or (
                triple[0] in "01" and triple[1] in "LR" and triple[2] in "ABCDEF"
            )
            table[(chr(ord("A") + i), symbol)] = (
                None if triple == "---" else (int(triple[0]), triple[1], triple[2])
            )
    return table


def physical_step(table, state, head, ones):
    action = table[(state, int(head in ones))]
    if action is None:
        return None
    write, direction, next_state = action
    if write:
        ones.add(head)
    else:
        ones.discard(head)
    return next_state, head + (1 if direction == "R" else -1)


def g(k, c):
    while c < 2 * k:
        k, c = k - (c // 2 + 1), 2 * c + 3
    if c <= 2 * k + 1:
        return 0, 2 * c + 3
    return 4 * k + 4, c - 2 * k - 2


def t(a, c):
    if c == 0:
        return (2, a + 1), "zero"
    if c == 1:
        return (a + 2, 0), "one"
    if a % 2 == 0:
        return (a + 3, c - 2), "even"
    if c == 2:
        return None, "halt"
    if c == 3:
        return g(a // 2, 1), "odd-three-drain"
    return g(a // 2 + 1, c - 2), "odd-large-drain"


def p1_cells(a, c, head):
    return set(range(head - a, head + c))


def verify_segment(table, a, c, state, head, ones):
    predicted, branch = t(a, c)
    assert state == "A" and ones == p1_cells(a, c, head)
    for defined_steps in range(RAW_FUEL + 1):
        action = physical_step(table, state, head, ones)
        if action is None:
            assert predicted is None, (
                "premature raw halt", (a, c), branch, defined_steps, predicted
            )
            return state, head, ones, defined_steps, branch
        assert defined_steps != RAW_FUEL, ("fuel exceeded", (a, c), predicted)
        state, head = action
        if predicted is not None and state == "A" and ones == p1_cells(
            *predicted, head
        ):
            return state, head, ones, defined_steps + 1, branch
    raise AssertionError("unreachable fuel fallthrough")


def main():
    table = parse_rle(RLE)
    branches = Counter()
    maximum = (0, None)
    for a in range(MAX_A + 1):
        for c in range(MAX_C + 1):
            state, head, ones = "A", 0, p1_cells(a, c, 0)
            _, _, _, steps, branch = verify_segment(table, a, c, state, head, ones)
            branches[branch] += 1
            if steps > maximum[0]:
                maximum = steps, (a, c)
    state, head, ones = "A", 0, set()
    for _ in range(6):
        next_state = physical_step(table, state, head, ones)
        assert next_state is not None
        state, head = next_state
    assert state == "A" and head == 0 and ones == {-2, -1, 0}
    current = (2, 1)
    raw_steps = 6
    for index in range(BLANK_MACRO_STEPS):
        state, head, ones, segment_steps, branch = verify_segment(
            table, *current, state, head, ones
        )
        raw_steps += segment_steps
        branches["blank_" + branch] += 1
        current, _ = t(*current)
        assert current is not None, ("unexpected halt", index)
    print("RLE =", RLE)
    print("synthetic_P1_configs =", (MAX_A + 1) * (MAX_C + 1))
    print("branch_counts =", dict(sorted(branches.items())))
    print("largest_synthetic_segment_defined_steps =", maximum)
    print("blank_prefix_macro_steps =", BLANK_MACRO_STEPS)
    print("blank_prefix_raw_steps =", raw_steps)
    print("blank_prefix_final_hub =", current)
    print("all_checks = PASS; no nonhalting conclusion")


if __name__ == "__main__":
    main()
