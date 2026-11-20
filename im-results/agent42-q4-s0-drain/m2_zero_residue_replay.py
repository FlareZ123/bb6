#!/usr/bin/env python3
"""Finite replay of the TM63 marker-2, n=0 (mod 8) source increment.

This is an independent deterministic experiment, not a proof.  It checks the
full original-TM2 transition sequence, exact step count, and complete endpoint
tape against the S1Encoder configuration for 640 small parameter choices.
The tested family is the one used by M2EvenResidueZeroCounted.lean.
"""

from dataclasses import dataclass

D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)


def marker(m: int) -> tuple[bool, ...]:
    return ((False, True) if m % 3 == 0 else
            (True, False, True) if m % 3 == 1 else
            (True, True, False, True))


def bin_dec(length: int, value: int) -> tuple[bool, ...]:
    # Complement-coded binary blocks, matching S1Encoder.binDec.
    p = (1 << (length + 1)) - 1 - value
    out: list[bool] = []
    for _ in range(length):
        if p <= 1:
            break
        out.extend(D0 if p % 2 == 0 else D1)
        p //= 2
    return tuple(out)


def s1_config(L: int, n: int, m: int, a: int, r: int, b: int,
              head: int = 0) -> "Config":
    left = bin_dec(a, r) + marker(m) + D0 + bin_dec(L, n) + LH
    right = (False, True, True, True, False, False) + D1 * (b + 1)
    ones: set[int] = set()
    for i, bit in enumerate(left):
        if bit:
            ones.add(head - i)
    for i, bit in enumerate(right):
        if bit:
            ones.add(head + 1 + i)
    return Config(3, head, ones)


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


def same_config(x: Config, y: Config) -> bool:
    return (x.state == y.state and x.head == y.head and x.ones == y.ones)


def v2(n: int) -> int:
    assert n > 0
    result = 0
    while n % 2 == 0:
        n //= 2
        result += 1
    return result


def proposed_increment_cost_marker2(n: int, a: int, b: int) -> int:
    # proposedIncrementCost 2 n a b, with v2(n) explicit.
    return (6 * (4 ** b) + 42 * (2 ** b) + 15 + 8
            + 12 * (a + v2(n)) - 9 * b)


def check_small_parameters() -> tuple[int, int]:
    checked = 0
    total_steps = 0
    for q in range(1, 33):
        n = 8 * q
        L = n.bit_length()  # minimal width satisfying n < 2^L
        assert L >= 4 and n < (1 << L)
        for a in range(1, 5):
            for b in range(0, 5):
                cost = proposed_increment_cost_marker2(n, a, b)
                source = s1_config(L, n, 2, a, 0, b)
                run(source, cost)

                target = s1_config(
                    L, n - 1, 1, a + b + 2, 0, (1 << b) - 1,
                    5 + 3 * b,
                )
                if not same_config(source, target):
                    raise AssertionError(
                        f"endpoint mismatch: q={q}, L={L}, a={a}, b={b}, "
                        f"cost={cost}; got=({source.state},{source.head},"
                        f"{len(source.ones)} ones), expected="
                        f"({target.state},{target.head},{len(target.ones)} ones)"
                    )
                checked += 1
                total_steps += cost
    return checked, total_steps


if __name__ == "__main__":
    count, steps = check_small_parameters()
    print(f"TM63 marker-2 zero-residue replay: PASS ({count} cases)")
    print(f"Exact simulated transitions: {steps}")
