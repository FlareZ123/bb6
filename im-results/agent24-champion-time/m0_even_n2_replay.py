#!/usr/bin/env python3
"""Literal TM2 replay for the m=0,n=2 even reset stage.

Reproduces the fixed 39-step bridge, its parameterized left-sweep input,
the q4 cut, the complete reset-prefix endpoint, and the counted drain.
This is computational evidence, not a proof.  The transition table is
copied from BB6Coverage.Agent48Champion.tm2 in ChampionRootBridge.lean.

Run with: python3 m0_even_n2_replay.py
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)
RIGHT_GUARD = (False, True, True, True, False, False)

# (write bit, head displacement, next state); None denotes halt.
TM2 = (
    ((True, +1, 1), None),
    ((True, -1, 2), (False, +1, 5)),
    ((True, +1, 4), (False, -1, 3)),
    ((False, -1, 2), (True, +1, 1)),
    ((True, +1, 0), (True, +1, 4)),
    ((True, +1, 4), (False, +1, 3)),
)


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
    }[m]


def d1pow(n: int) -> tuple[bool, ...]:
    return D1 * n


def bin_dec(length: int, value: int) -> tuple[bool, ...]:
    """S1Encoder.binDec: binaryCounterFuel length (2^(length+1)-1-value)."""
    p = 2 ** (length + 1) - 1 - value
    out: list[bool] = []
    for _ in range(length):
        if p <= 1:
            break
        out.extend(D0 if p % 2 == 0 else D1)
        p //= 2
    return tuple(out)


def config_from_words(left: tuple[bool, ...], right: tuple[bool, ...],
                      head: int = 0) -> Config:
    ones = {head - i for i, bit in enumerate(left) if bit}
    ones.update(head + 1 + i for i, bit in enumerate(right) if bit)
    return Config(3, head, ones)


def source_config(a: int, b: int) -> Config:
    left = d1pow(a) + marker_word(0) + D0 + bin_dec(3, 2) + LH
    right = RIGHT_GUARD + d1pow(b + 1)
    return config_from_words(left, right)


def reset_prefix_target(a: int, b: int) -> Config:
    new_a = a + b + 1
    new_z = 2**b - 1
    left = (bin_dec(new_a, new_z) + marker_word(2) + D0
            + bin_dec(3, 1) + LH)
    right = RIGHT_GUARD + d1pow(1)
    return config_from_words(left, right, head=5 + 3 * b)


def counted_increment_target(a: int, b: int) -> Config:
    new_a = a + b + 1
    right_count = 2**b - 1
    left = (bin_dec(new_a, 0) + marker_word(2) + D0
            + bin_dec(3, 1) + LH)
    right = RIGHT_GUARD + d1pow(right_count + 1)
    return config_from_words(left, right, head=5 + 3 * b)


def step(c: Config) -> Optional[Config]:
    transition = TM2[c.state][1 if c.head in c.ones else 0]
    if transition is None:
        return None
    write, move, next_state = transition
    ones = set(c.ones)
    if write:
        ones.add(c.head)
    else:
        ones.discard(c.head)
    return Config(next_state, c.head + move, ones)


def run(c: Config, steps: int) -> tuple[Optional[Config], list[int]]:
    heads = [c.head]
    for _ in range(steps):
        nxt = step(c)
        if nxt is None:
            return None, heads
        c = nxt
        heads.append(c.head)
    return c, heads


def exact_window(c: Config, origin: int, lo: int, hi: int,
                 marked: set[int]) -> bool:
    actual = {x - origin for x in c.ones if origin + lo <= x <= origin + hi}
    return actual == marked


def q4_right_shape(c: Config, b: int) -> bool:
    if c.state != 4 or c.head != 0:
        return False
    if not all(i in c.ones for i in range(5)):
        return False
    if 5 in c.ones or 6 in c.ones:
        return False
    if not all(7 + i in c.ones for i in range(3 * (b + 1))):
        return False
    return not any(x >= 10 + 3 * b for x in c.ones)


def drain_cost(b: int) -> int:
    # drainCost (2^b-1) = 6*4^b + 42*2^b - 12*b - 48.
    return 6 * 4**b + 42 * 2**b - 12 * b - 48


def check_bridge() -> None:
    start = Config(3, 0, {-7, -6, -5, -4, -1, 2, 3})
    end, heads = run(start, 39)
    assert end is not None
    assert (end.state, end.head, end.ones) == (
        4, 3, {-9, -8, -7, -4, -1, 1, 2, 3}
    )
    assert all(-9 <= h <= 2 for h in heads[:-1])


def check_q4_cut(a: int, b: int) -> None:
    c, _ = run(source_config(a, b), 36 + 12 * a)
    assert c is not None and q4_right_shape(c, b)
    left = (True,) + d1pow(a - 1) + marker_word(2) + D0 + bin_dec(3, 1) + LH
    assert all(((-i) in c.ones) == bit for i, bit in enumerate(left))


def check_bridge_decomposition(a: int, b: int) -> None:
    c, _ = run(source_config(a, b), 9 * a)
    assert c is not None and (c.state, c.head) == (3, -3 * a)
    start_window = {-7, -6, -5, -4, -1, 2, 3}
    assert exact_window(c, -3 * a, -9, 3, start_window)

    c, heads = run(c, 39)
    assert c is not None and (c.state, c.head) == (4, -3 * a + 3)
    end_window = {-9, -8, -7, -4, -1, 1, 2, 3}
    assert exact_window(c, -3 * a, -9, 3, end_window)
    assert all(-9 <= h + 3 * a <= 2 for h in heads[:-1])

    c, _ = run(c, 3 * (a - 1))
    assert c is not None and (c.state, c.head) == (4, 0)
    assert q4_right_shape(c, b)


def check_reset_prefix(a: int, b: int) -> None:
    steps = 75 + 12 * a + 3 * b
    out, _ = run(source_config(a, b), steps)
    target = reset_prefix_target(a, b)
    assert out is not None
    assert (out.state, out.head, out.ones) == (
        target.state, target.head, target.ones
    )


def check_counted_increment(a: int, b: int) -> None:
    prefix = 75 + 12 * a + 3 * b
    total = prefix + drain_cost(b)
    out, _ = run(source_config(a, b), total)
    target = counted_increment_target(a, b)
    assert out is not None
    assert (out.state, out.head, out.ones) == (
        target.state, target.head, target.ones
    )


def main() -> None:
    assert bin_dec(3, 2) == D1 + D0 + D1
    assert bin_dec(3, 1) == D0 + D1 + D1
    check_bridge()

    decomposition_cases = 0
    cut_cases = 0
    reset_cases = 0
    counted_cases = 0
    for a in range(1, 9):
        for b in range(6):
            check_bridge_decomposition(a, b)
            check_q4_cut(a, b)
            check_reset_prefix(a, b)
            decomposition_cases += 1
            cut_cases += 1
            reset_cases += 1
            if a <= 5 and b <= 4:
                check_counted_increment(a, b)
                counted_cases += 1

    print("m=0,n=2 even q4 replay: PASS")
    print("finite bridge: 39 exact steps, heads confined to [-9,2]")
    print(f"bridge decomposition: {decomposition_cases} cases")
    print(f"q4 cut shape/left stream: {cut_cases} cases")
    print(f"full reset prefix: {reset_cases} cases")
    print(f"counted increment with closed drain cost: {counted_cases} cases")
    print("prefix cost: 36 + 12*a")
    print("reset-prefix cost: 75 + 12*a + 3*b")


if __name__ == "__main__":
    main()
