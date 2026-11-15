#!/usr/bin/env python3
"""Finite-support replay for the candidate TM63 m=1, n=8*k+4 reset row.

The tape is an exact set of one-cells; every unlisted integer cell is blank.
This is a deterministic simulator, not a proof of the quantified source theorem.
Run: python3 replay.py
"""
from dataclasses import dataclass

# Each entry is (write_bit, displacement, next_state); displacement is ±1.
TM2 = (
    ((True, +1, 1), None),
    ((True, -1, 2), (False, +1, 5)),
    ((True, +1, 4), (False, -1, 3)),
    ((False, -1, 2), (True, +1, 1)),
    ((True, +1, 0), (True, +1, 4)),
    ((True, +1, 4), (False, +1, 3)),
)
D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)


@dataclass(frozen=True)
class Config:
    state: int
    head: int
    ones: frozenset[int]


def marker_word(m: int) -> tuple[bool, ...]:
    m %= 3
    if m == 0:
        return (False, True)
    if m == 1:
        return (True, False, True)
    return (True, True, False, True)


def bin_dec(length: int, n: int) -> tuple[bool, ...]:
    assert length >= 0 and 0 <= n < 2**length
    p = 2 ** (length + 1) - 1 - n
    out: list[bool] = []
    for _ in range(length):
        if p <= 1:
            break
        out.extend(D0 if p % 2 == 0 else D1)
        p //= 2
    return tuple(out)


def s1_config(L: int, n: int, m: int, a: int, z: int,
              b: int, h: int = 0) -> Config:
    assert L >= 0 and 0 <= n < 2**L
    assert 0 <= z < 2**a
    left = bin_dec(a, z) + marker_word(m) + D0 + bin_dec(L, n) + LH
    right = (False, True, True, True, False, False) + D1 * (b + 1)
    ones = {h - i for i, bit in enumerate(left) if bit}
    ones.update(h + 1 + i for i, bit in enumerate(right) if bit)
    return Config(3, h, frozenset(ones))


def step(c: Config) -> Config | None:
    bit = c.head in c.ones
    transition = TM2[c.state][1 if bit else 0]
    if transition is None:
        return None
    write, displacement, next_state = transition
    ones = set(c.ones)
    if write:
        ones.add(c.head)
    else:
        ones.discard(c.head)
    return Config(next_state, c.head + displacement, frozenset(ones))


def run(c: Config, count: int) -> Config | None:
    for _ in range(count):
        c = step(c)
        if c is None:
            return None
    return c


def run_with_heads(c: Config, count: int):
    heads = [c.head]
    for _ in range(count):
        c = step(c)
        if c is None:
            return None, heads
        heads.append(c.head)
    return c, heads


BRIDGE_START = frozenset(
    (-10, -9, -8, -7, -6, -5, -4, -1, 2, 3, 4, 5)
)
BRIDGE_END = frozenset(
    (-12, -11, -10, -7, -4, -1, 1, 2, 3, 4, 5)
)


def check_finite_bridge() -> None:
    start = Config(3, 0, BRIDGE_START)
    end, heads = run_with_heads(start, 53)
    assert end == Config(4, 5, BRIDGE_END)
    assert all(-12 <= h <= 5 for h in heads)


def check_case(L: int, k: int, a: int, b: int) -> None:
    n = 8 * k + 4
    start = s1_config(L, n, 1, a, 0, b)
    sweep, _ = run_with_heads(start, 9 * a + 3)
    assert sweep is not None
    assert sweep.state == 3 and sweep.head == -(3 * a + 1)

    # Exact bridge-input frame, relative to the post-sweep head.
    for rel in range(-12, 6):
        assert ((sweep.head + rel) in sweep.ones) == (rel in BRIDGE_START)

    bridge, heads = run_with_heads(sweep, 53)
    assert bridge is not None
    assert bridge.state == 4 and bridge.head == sweep.head + 5
    assert all(-12 <= h - sweep.head <= 5 for h in heads)
    for rel in range(-12, 6):
        assert ((sweep.head + rel) in bridge.ones) == (rel in BRIDGE_END)

    # The following 3*a state-4 moves are the unchanged one-scan.
    after_prefix, _ = run_with_heads(start, 56 + 12 * a)
    assert after_prefix is not None
    assert after_prefix.state == 4 and after_prefix.head == 4

    source_left = (
        (True,) + (True,) * (3 * a) + marker_word(0)
        + D0 + D0 + D0 + D1 + bin_dec(L - 3, k) + LH
    )
    for i, bit in enumerate(source_left):
        assert ((after_prefix.head - i) in after_prefix.ones) == bit

    # q4RightShape at the original head h=0.
    assert all(i in after_prefix.ones for i in range(5))
    assert 5 not in after_prefix.ones and 6 not in after_prefix.ones
    assert all(7 + i in after_prefix.ones for i in range(3 * (b + 1)))
    assert all(10 + 3 * b + i not in after_prefix.ones for i in range(5))

    # Full reset-prefix endpoint; this is not yet the counted drain.
    total = 91 + 12 * a + 3 * b
    out = run(start, total)
    target = s1_config(
        L, n - 1, 0, a + b + 2, 2**b - 1, 0, 5 + 3 * b
    )
    assert out == target, (L, k, a, b, out, target)


def main() -> None:
    check_finite_bridge()
    count = 0
    for L in range(3, 9):
        k = 0
        while 8 * k + 4 < 2**L:
            for a in range(4):
                for b in range(3):
                    check_case(L, k, a, b)
                    count += 1
            k += 1
    assert count == 756
    print("finite bridge: 53 moves; heads confined to [-12,5]")
    print(f"reset-prefix replay: {count} parameter cases passed")


if __name__ == "__main__":
    main()
