#!/usr/bin/env python3
"""Independent raw-step test for the synthetic P1 halting-funnel family.

Lean proves the accelerated map's halting behavior for all n. This script only
tests finite raw TM traces and checks an inferred raw-step closed form.
"""
from __future__ import annotations

MACHINE = "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"
TRANSITIONS = tuple((part[:3], part[3:]) for part in MACHINE.split("_"))
EXPECTED = (36, 200, 924, 3944, 16260, 65984, 265788, 1066808, 4274484)


def run_raw(a: int) -> int:
    """TM initially in P1(a,0): head 0, state A, 1s at [-a,-1]."""
    tape = set(range(-a, 0))
    head = 0
    state = 0
    steps = 0
    while True:
        instruction = TRANSITIONS[state][int(head in tape)]
        if instruction == "---":
            assert state == 5 and head == 2
            return steps
        if instruction[0] == "1":
            tape.add(head)
        else:
            tape.discard(head)
        head += 1 if instruction[1] == "R" else -1
        state = ord(instruction[2]) - ord("A")
        steps += 1


def main() -> None:
    for n, expected in enumerate(EXPECTED):
        a = 14 * 2**n - 2 * n - 11
        result = run_raw(a)
        predicted, remainder = divmod(
            196 * 4**n - 84 * 2**n - 12 * n - 4, 3
        )
        assert remainder == 0
        assert predicted == expected == result, (n, result, predicted, expected)
        print(f"n={n:2d}, P1({a},0): raw steps={result}")
    print("All nine finite cases reproduced. No all-n raw-step theorem claimed.")


if __name__ == "__main__":
    main()
