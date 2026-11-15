#!/usr/bin/env python3
"""Deterministic replay for the m=1, n=8*q+7 reset row.

This is experimental corroboration, not the formal proof. The 26-step
finite bridge is separately imported from M1OddQ4Bridge.lean.
"""

from dataclasses import dataclass

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


def q4_right_facing(b: int) -> tuple[bool, ...]:
    return (True, True, True, True, False, False) + D1 * (b + 1)


def s1_config(length: int, n: int, m: int, a: int, z: int, b: int,
              head: int = 0) -> Config:
    left = bin_dec(a, z) + marker_word(m) + D0 + bin_dec(length, n) + LH
    right = right_facing(b)
    ones = {head - i for i, bit in enumerate(left) if bit}
    ones.update(head + 1 + i for i, bit in enumerate(right) if bit)
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


def run(c: Config, steps: int) -> list[int]:
    heads = []
    for i in range(steps):
        heads.append(c.head)
        if not step(c):
            raise AssertionError(f"halted after {i} of {steps} requested steps")
    return heads


def left_stream(c: Config, length: int) -> tuple[bool, ...]:
    return tuple(c.head - i in c.ones for i in range(length))


def right_stream(c: Config, length: int) -> tuple[bool, ...]:
    return tuple(c.head + 1 + i in c.ones for i in range(length))


def q4_left_facing(length: int, n: int, a: int) -> tuple[bool, ...]:
    return ((True,) + D1 * a + marker_word(0) + D0
            + bin_dec(length, n) + LH)


def same_config(c: Config, expected: Config) -> bool:
    return (c.state == expected.state and c.head == expected.head
            and c.ones == expected.ones)


def check_bridge() -> None:
    start = Config(3, 0, {-4, -1})
    end = Config(4, 2, {1, -1, -4, -5, -6})
    c = Config(start.state, start.head, set(start.ones))
    heads = run(c, 26)
    assert same_config(c, end), (c, end)
    assert min(heads) >= -6 and max(heads) <= 1


def check_case(q: int, a: int, b: int) -> None:
    n = 8 * q + 7
    length = n.bit_length()
    c = s1_config(length, n, 1, a, 0, b)

    prefix_cost = 28 + 12 * a
    run(c, prefix_cost)
    assert c.state == 4 and c.head == 0
    assert left_stream(c, len(q4_left_facing(length, n - 1, a))) == \
        q4_left_facing(length, n - 1, a)
    assert right_stream(c, len(q4_right_facing(b))) == q4_right_facing(b)

    suffix_cost = 39 + 3 * b
    run(c, suffix_cost)
    mid = s1_config(length, n - 1, 0, a + b + 2, 2**b - 1, 0,
                    head=5 + 3 * b)
    assert same_config(c, mid), (q, a, b, "q4 suffix", c, mid)

    drain_cost = 6 * 4**b + 42 * 2**b - 12 * b - 48
    run(c, drain_cost)
    final = s1_config(length, n - 1, 0, a + b + 2, 0, 2**b - 1,
                      head=5 + 3 * b)
    assert same_config(c, final), (q, a, b, "counted drain", c, final)

    expected = 6 * 4**b + 42 * 2**b + 19 + 12 * a - 9 * b
    assert prefix_cost + suffix_cost + drain_cost == expected


def main() -> None:
    check_bridge()
    cases = 0
    for q in range(4):
        for a in (1, 2):
            for b in (0, 1, 2):
                check_case(q, a, b)
                cases += 1
    print(f"PASS: exact 26-step bridge and {cases} parameterized reset cases")


if __name__ == "__main__":
    main()
