#!/usr/bin/env python3
"""Exact finite-support replay of the TM63 q4 root endpoint.

Transcribes BB6Coverage.Agent48Champion.tm2 and the S1Encoder definitions
for d0/d1, markerWord, lh, binDec, s1LeftFacing, and s1RightFacing.
The tape is represented by the complete set of marked Int coordinates;
all unlisted cells are blank, so there is no finite-window truncation.
"""
from __future__ import annotations

from dataclasses import dataclass

D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)


def marker_word(m: int) -> tuple[bool, ...]:
    r = m % 3
    if r == 0:
        return (False, True)
    if r == 1:
        return (True, False, True)
    return (True, True, False, True)


def binary_counter_fuel(fuel: int, p: int) -> tuple[bool, ...]:
    if fuel == 0 or p <= 1:
        return ()
    if p % 2 == 0:
        return D0 + binary_counter_fuel(fuel - 1, p // 2)
    return D1 + binary_counter_fuel(fuel - 1, p // 2)


def bin_dec(length: int, n: int) -> tuple[bool, ...]:
    return binary_counter_fuel(length, 2 ** (length + 1) - 1 - n)


def s1_left_facing(L: int, n: int, m: int, a: int, z: int) -> tuple[bool, ...]:
    return bin_dec(a, z) + marker_word(m) + D0 + bin_dec(L, n) + LH


def s1_right_facing(b: int) -> tuple[bool, ...]:
    return (False, True, True, True, False, False) + D1 * (b + 1)


def s1_marks(L: int, n: int, m: int, a: int, z: int, b: int, h: int) -> set[int]:
    left = s1_left_facing(L, n, m, a, z)
    right = s1_right_facing(b)
    return ({h - i for i, bit in enumerate(left) if bit}
            | {h + 1 + i for i, bit in enumerate(right) if bit})


# Exact twelve-slot tm2 table from ChampionRootBridge.lean.
# Each defined row is (next_state, write_bit, move_right).
TM2 = {
    (0, False): (1, True, True),
    (0, True): None,
    (1, False): (2, True, False),
    (1, True): (5, False, True),
    (2, False): (4, True, True),
    (2, True): (3, False, False),
    (3, False): (2, False, False),
    (3, True): (1, True, True),
    (4, False): (0, True, True),
    (4, True): (4, True, True),
    (5, False): (4, True, True),
    (5, True): (3, False, True),
}


@dataclass
class Config:
    state: int
    head: int
    marks: set[int]


def run(c: Config, steps: int) -> tuple[Config, list[tuple[int, int, int, int]]]:
    trace: list[tuple[int, int, int, int]] = []
    for step in range(steps):
        read = c.head in c.marks
        action = TM2[(c.state, read)]
        if action is None:
            raise AssertionError(f"halt at primitive step {step}")
        next_state, write, right = action
        if write:
            c.marks.add(c.head)
        else:
            c.marks.discard(c.head)
        c.head += 1 if right else -1
        c.state = next_state
        trace.append((step + 1, c.state, c.head, len(c.marks)))
    return c, trace


def main() -> None:
    start_marks = s1_marks(3, 7, 2, 6, 0, 63, 29)
    # Independent initial-root witness already recorded in InitialS1RootWitness.md.
    initial_witness = (
        [31, 32, 33]
        + [36 + i for i in range(192)]
        + [29 - i for i in range(18)]
        + [11, 10, 8, 5, 2, -1, -4, -5, -6, -8, -9, -10]
    )
    assert len(initial_witness) == 225 and len(set(initial_witness)) == 225
    assert start_marks == set(initial_witness)

    target_marks = s1_marks(3, 6, 1, 71, 2**63 - 1, 0, 223)
    assert len(s1_left_facing(3, 6, 1, 71, 2**63 - 1)) == 234
    assert len(s1_right_facing(0)) == 9

    final, trace = run(Config(3, 29, set(start_marks)), 332)
    difference = final.marks ^ target_marks
    assert (final.state, final.head) == (3, 223)
    assert final.marks == target_marks
    assert not difference
    assert (min(final.marks), max(final.marks)) == (-10, 232)

    print("steps=332")
    print(f"endpoint_state={final.state}")
    print(f"endpoint_head={final.head}")
    print(f"marked_count={len(final.marks)}")
    print(f"support=[{min(final.marks)},{max(final.marks)}]")
    print("symmetric_difference_count=0")
    print("marked_cells=" + repr(sorted(final.marks)))
    print("last_10=" + repr(trace[-10:]))


if __name__ == "__main__":
    main()
