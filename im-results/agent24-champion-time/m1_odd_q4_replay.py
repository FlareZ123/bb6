#!/usr/bin/env python3
"""Independent literal-table replay for the TM63 m=1,n=3 odd q4 reset.

This is reproducible computational evidence, not a proof.  The 12-entry
transition table below is copied from BB6Coverage.Agent48Champion.tm2 in
ChampionRootBridge.lean.  The encoder follows S1Encoder.lean exactly:
d0=(001), d1=(111), markerWord(0)=(01), markerWord(1)=(101), and the
S0 right physical word is (011100) followed by d1^(b+1).

Run with: python3 m1_odd_q4_replay.py
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)
RIGHT_GUARD = (False, True, True, True, False, False)

# Each entry is (write_bit, move_delta, next_state); None is halt.
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
        if p % 2 == 0:
            out.extend(D0)
        else:
            out.extend(D1)
        p //= 2
    return tuple(out)


def config_from_words(left: tuple[bool, ...], right: tuple[bool, ...],
                      head: int = 0) -> Config:
    ones = {head - i for i, bit in enumerate(left) if bit}
    ones.update(head + 1 + i for i, bit in enumerate(right) if bit)
    return Config(3, head, ones)


def source_config(a: int, b: int) -> Config:
    left = d1pow(a) + marker_word(1) + D0 + bin_dec(3, 3) + LH
    right = RIGHT_GUARD + d1pow(b + 1)
    return config_from_words(left, right)


def reset_prefix_target(a: int, b: int) -> Config:
    new_a = a + b + 2
    new_z = 2**b - 1
    left = (bin_dec(new_a, new_z) + marker_word(0) + D0
            + bin_dec(3, 2) + LH)
    right = RIGHT_GUARD + d1pow(1)
    return config_from_words(left, right, head=5 + 3 * b)


def step(c: Config) -> Optional[Config]:
    bit = c.head in c.ones
    transition = TM2[c.state][1 if bit else 0]
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


def expect_word(c: Config, origin: int, bits: tuple[bool, ...],
                direction: int) -> bool:
    return all(((origin + direction * i) in c.ones) == bit
               for i, bit in enumerate(bits))


def check_finite_bridge() -> None:
    start = Config(3, 0, {-7, -4, -1, 2, 3, 4})
    end, heads = run(start, 29)
    assert end is not None
    assert (end.state, end.head, end.ones) == (
        4, 5, {4, 3, 2, 1, -1, -4, -5, -6, -7}
    )
    assert all(-9 <= h <= 4 for h in heads[:-1])


def check_prefix_cut(a: int, b: int) -> None:
    out, _ = run(source_config(a, b), 32 + 12 * a)
    assert out is not None and (out.state, out.head) == (4, 4)
    q4_left = ((True,) + d1pow(a) + marker_word(0) + D0
               + bin_dec(3, 2) + LH)
    assert expect_word(out, 0, q4_left, -1)
    assert all(x in out.ones for x in range(0, 5))
    assert 5 not in out.ones and 6 not in out.ones
    assert all(7 + i in out.ones for i in range(3 * (b + 1)))
    assert all(10 + 3 * b + i not in out.ones for i in range(5))


def check_full_reset_prefix(a: int, b: int) -> None:
    steps = 67 + 12 * a + 3 * b
    out, _ = run(source_config(a, b), steps)
    target = reset_prefix_target(a, b)
    assert out is not None
    assert (out.state, out.head, out.ones) == (
        target.state, target.head, target.ones
    )


def main() -> None:
    assert bin_dec(3, 3) == D0 + D0 + D1
    assert bin_dec(3, 2) == D1 + D0 + D1
    check_finite_bridge()
    prefix_cases = 0
    full_cases = 0
    for a in range(9):
        for b in range(9):
            check_full_reset_prefix(a, b)
            full_cases += 1
            if a <= 5 and b <= 5:
                check_prefix_cut(a, b)
                prefix_cases += 1
    print("m=1,n=3 odd q4 replay: PASS")
    print(f"finite bridge: 29 exact steps, heads confined to [-9,4]")
    print(f"prefix cut: {prefix_cases} exact tape/shape cases")
    print(f"full reset prefix: {full_cases} exact tape cases")
    print("cost: 67 + 12*a + 3*b = resetPrefixCost(1,3,a,b)")


if __name__ == "__main__":
    main()
