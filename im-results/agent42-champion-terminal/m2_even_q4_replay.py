#!/usr/bin/env python3
"""Deterministic replay for the TM63 m=2,n=4 even q4 branch.

This is a finite experimental check, not a proof.  Unlisted tape cells are
blank.  The transition table is the original TM63 table used by
ChampionRootBridge.lean.  The script checks the 50-step bridge, the
parameterized q4 cut, and the complete reset-plus-drain endpoint for small
a,b.
"""

from dataclasses import dataclass
from typing import Optional

D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)


def marker(m: int) -> tuple[bool, ...]:
    return ((False, True) if m % 3 == 0 else
            (True, False, True) if m % 3 == 1 else
            (True, True, False, True))


def bin_dec(length: int, value: int) -> tuple[bool, ...]:
    p = (1 << (length + 1)) - 1 - value
    out: list[bool] = []
    for _ in range(length):
        if p <= 1:
            break
        if p % 2 == 0:
            out.extend(D0)
        else:
            out.extend(D1)
        p //= 2
    return tuple(out)


def left_facing(L: int, n: int, m: int, a: int, z: int):
    return bin_dec(a, z) + marker(m) + D0 + bin_dec(L, n) + LH


def right_facing(b: int):
    return (False, True, True, True, False, False) + D1 * (b + 1)


@dataclass
class Config:
    state: int
    head: int
    ones: set[int]


# Each defined entry is (write, move_right, next_state).
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


def s1_config(L: int, n: int, m: int, a: int, z: int,
              b: int, head: int = 0) -> Config:
    ones: set[int] = set()
    for i, bit in enumerate(left_facing(L, n, m, a, z)):
        if bit:
            ones.add(head - i)
    for i, bit in enumerate(right_facing(b)):
        if bit:
            ones.add(head + 1 + i)
    return Config(3, head, ones)


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


def run(c: Config, steps: int) -> None:
    for k in range(steps):
        if not step(c):
            raise AssertionError(f"machine halted at step {k}")


def tape_bit(c: Config, x: int) -> bool:
    return x in c.ones


def left_stream(c: Config, length: int) -> tuple[bool, ...]:
    return tuple(tape_bit(c, c.head - i) for i in range(length))


def right_stream(c: Config, length: int) -> tuple[bool, ...]:
    return tuple(tape_bit(c, c.head + 1 + i) for i in range(length))


def q4_left_facing(a: int):
    return ((True,) + D1 * a + marker(1) + D0 +
            bin_dec(3, 3) + LH)


def q4_right_facing(b: int):
    return (True, True, True, True, False, False) + D1 * (b + 1)


def expected_final(a: int, b: int, h: int = 0) -> Config:
    return s1_config(3, 3, 1, a + b + 2, 0, (1 << b) - 1,
                     h + 5 + 3 * b)


def total_increment_cost(a: int, b: int) -> int:
    # proposedIncrementCost 2 4 a b
    return (6 * (4 ** b) + 42 * (2 ** b) + 47 + 12 * a - 9 * b)


def check_bridge() -> None:
    c = Config(3, 0, {-10, -9, -8, -7, -6, -5, -4, -1, 2})
    visited = []
    for _ in range(50):
        visited.append(c.head)
        assert step(c)
    assert (c.state, c.head) == (4, 2)
    assert c.ones == {1, -1, -4, -7, -10, -11, -12, 2}
    assert min(visited) >= -12 and max(visited) <= 2


def check_small_parameters(max_a: int = 4, max_b: int = 4) -> int:
    checked = 0
    for a in range(max_a + 1):
        for b in range(max_b + 1):
            source = s1_config(3, 4, 2, a, 0, b)
            prefix = 56 + 12 * a
            run(source, prefix)
            assert (source.state, source.head) == (4, 0)
            assert left_stream(source, len(q4_left_facing(a))) == q4_left_facing(a)
            assert right_stream(source, len(q4_right_facing(b))) == q4_right_facing(b)

            # Continue from the q4 cut through its 39+3*b suffix and drain.
            run(source, 39 + 3 * b)
            assert (source.state, source.head) == (3, 5 + 3 * b)
            run(source, 6 * (4 ** b) + 42 * (2 ** b) - 12 * b - 48)
            target = expected_final(a, b)
            assert source.state == target.state
            assert source.head == target.head
            assert source.ones == target.ones

            # Re-run the full source transition with the closed cost formula.
            direct = s1_config(3, 4, 2, a, 0, b)
            run(direct, total_increment_cost(a, b))
            assert direct.state == target.state
            assert direct.head == target.head
            assert direct.ones == target.ones
            checked += 1
    return checked


if __name__ == "__main__":
    check_bridge()
    count = check_small_parameters()
    print(f"50-step bridge: PASS; head interval [-12,2]")
    print(f"m=2,n=4 reset-plus-drain replay: PASS ({count} parameter pairs, 0<=a,b<=4)")
