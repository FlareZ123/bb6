#!/usr/bin/env python3
"""Finite replay of the m=0, n=8*q+6 sector.

This is an experimental simulator for small parameters only. A surviving
200,000-step prefix is not a nonhalting proof, and minimal-width runs are not
the actual TM63 root configuration (whose tape width and counters are huge).
"""

from dataclasses import dataclass
import argparse
import csv
import sys

D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)

TM = {
    (0, False): (True, True, 1),
    (0, True): None,
    (1, False): (True, False, 2),
    (1, True): (False, True, 5),
    (2, False): (True, True, 4),
    (2, True): (False, False, 3),
    (3, False): (False, False, 2),
    (3, True): (True, True, 1),
    (4, False): (True, True, 0),
    (4, True): (True, True, 4),
    (5, False): (True, True, 4),
    (5, True): (False, True, 3),
}


@dataclass
class Config:
    state: int
    head: int
    ones: set[int]


def marker_word(m: int) -> tuple[bool, ...]:
    return {
        0: (False, True),
        1: (True, False, True),
        2: (True, True, False, True),
    }[m % 3]


def bin_dec(length: int, n: int) -> tuple[bool, ...]:
    p = (1 << (length + 1)) - 1 - n
    out: list[bool] = []
    for _ in range(length):
        if p <= 1:
            break
        out.extend(D0 if p % 2 == 0 else D1)
        p //= 2
    return tuple(out)


def right_facing(b: int) -> tuple[bool, ...]:
    return (False, True, True, True, False, False) + D1 * (b + 1)


def s1_config(length: int, n: int, m: int, a: int, z: int, b: int) -> Config:
    left = bin_dec(a, z) + marker_word(m) + D0 + bin_dec(length, n) + LH
    right = right_facing(b)
    ones = {-i for i, bit in enumerate(left) if bit}
    ones.update(1 + i for i, bit in enumerate(right) if bit)
    return Config(3, 0, ones)


def step(c: Config) -> bool:
    transition = TM[(c.state, c.head in c.ones)]
    if transition is None:
        return False
    write, move_right, next_state = transition
    if write:
        c.ones.add(c.head)
    else:
        c.ones.discard(c.head)
    c.head += 1 if move_right else -1
    c.state = next_state
    return True


def run(c: Config, max_steps: int) -> dict[str, int | bool]:
    min_head = max_head = c.head
    steps = 0
    while steps < max_steps and step(c):
        steps += 1
        min_head = min(min_head, c.head)
        max_head = max(max_head, c.head)
    halted = TM[(c.state, c.head in c.ones)] is None
    return {
        "steps": steps,
        "halted": halted,
        "state": c.state,
        "head": c.head,
        "ones": len(c.ones),
        "min_head": min_head,
        "max_head": max_head,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-steps", type=int, default=200_000)
    args = parser.parse_args()

    writer = csv.writer(sys.stdout)
    writer.writerow(["q", "L", "a", "b", *run(Config(0, 0, set()), 0).keys()])
    cases = []
    for q in range(4):
        n = 8 * q + 6
        L = n.bit_length()
        for b in (0, 1, 2):
            cases.append((q, L, 1, b))
    for L in (4, 5, 8, 12):
        for b in (0, 1, 2):
            cases.append((1, L, 1, b))

    seen = set()
    for q, L, a, b in cases:
        if (q, L, a, b) in seen:
            continue
        seen.add((q, L, a, b))
        result = run(s1_config(L, 8 * q + 6, 0, a, 0, b), args.max_steps)
        writer.writerow([q, L, a, b, *result.values()])


if __name__ == "__main__":
    main()
