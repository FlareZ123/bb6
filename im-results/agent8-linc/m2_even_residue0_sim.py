#!/usr/bin/env python3
"""Deterministic TM63 simulation for the candidate m=2, n=8*k reset prefix.

This is an intermediate computational check, not a proof.  It uses only
Python's standard library and the S1Encoder tape conventions documented in
im-results/agent8-s1-encoder/S1Encoder.lean.
"""

from __future__ import annotations

from math import ceil, log2

D0 = (False, False, True)
D1 = (True, True, True)
LH = (True, True, False, True, True, True)


def marker_word(m: int) -> tuple[bool, ...]:
    return {
        0: (False, True),
        1: (True, False, True),
        2: (True, True, False, True),
    }[m]


def d1pow(n: int) -> tuple[bool, ...]:
    return D1 * n


def bin_dec(length: int, n: int) -> tuple[bool, ...]:
    """S1Encoder.binDec: encode 2^(length+1)-1-n, low block first."""
    assert length >= 0 and 0 <= n < 2**length
    c = 2 ** (length + 1) - 1 - n
    out: list[bool] = []
    for _ in range(length):
        out.extend(D0 if c % 2 == 0 else D1)
        c //= 2
    return tuple(out)


def right_facing(b: int) -> tuple[bool, ...]:
    return (False, True, True, True, False, False) + d1pow(b + 1)


def config_tape(
    length: int,
    n: int,
    marker: int,
    a: int,
    z: int,
    b: int,
    head: int,
) -> dict[int, bool]:
    """The true cells of s1Config; all unlisted cells are blank."""
    left = bin_dec(a, z) + marker_word(marker) + D0 + bin_dec(length, n) + LH
    right = right_facing(b)
    tape: dict[int, bool] = {}
    for i, bit in enumerate(left):
        if bit:
            tape[head - i] = True
    for i, bit in enumerate(right):
        if bit:
            tape[head + 1 + i] = True
    return tape


# State order A,B,C,D,E,F = 0,1,2,3,4,5.
# Each transition is (write-symbol, head displacement, next state).
# R is +1 and L is -1 in S1Encoder's Int-coordinate convention.
TM63 = (
    ((True, +1, 1), None),             # A0, A1
    ((True, -1, 2), (False, +1, 5)),  # B0, B1
    ((True, +1, 4), (False, -1, 3)),  # C0, C1
    ((False, -1, 2), (True, +1, 1)),  # D0, D1
    ((True, +1, 0), (True, +1, 4)),   # E0, E1
    ((True, +1, 4), (False, +1, 3)), # F0, F1
)


def run(steps: int, tape: dict[int, bool], head: int, state: int):
    tape = dict(tape)
    for t in range(steps):
        transition = TM63[state][1 if tape.get(head, False) else 0]
        if transition is None:
            raise AssertionError(f"machine halted after {t} steps")
        write, delta, next_state = transition
        if write:
            tape[head] = True
        else:
            tape.pop(head, None)
        head += delta
        state = next_state
    return tape, head, state


def v2(n: int) -> int:
    assert n > 0
    count = 0
    while n % 2 == 0:
        n //= 2
        count += 1
    return count


def reset_prefix_cost(marker: int, n: int, a: int, b: int) -> int:
    return 63 + 4 * marker + 12 * (a + v2(n)) + 3 * b


def check_case(k: int, a: int, b: int, length: int) -> None:
    n = 8 * k
    assert k > 0 and a > 0 and n < 2**length
    head = 0
    steps = reset_prefix_cost(2, n, a, b)

    source = config_tape(length, n, 2, a, 0, b, head)
    actual, actual_head, actual_state = run(steps, source, head, 3)

    # Reset-prefix endpoint: the old right unary counter b has been moved
    # into the S1 left-side z parameter; the right-side b parameter is zero.
    target_head = head + 5 + 3 * b
    target = config_tape(
        length, n - 1, 1, a + b + 2, 2**b - 1, 0, target_head
    )

    if (actual_state, actual_head, actual) != (3, target_head, target):
        differing = sorted(
            x for x in set(actual) | set(target) if actual.get(x, False) != target.get(x, False)
        )
        raise AssertionError(
            f"failed k={k}, a={a}, b={b}, L={length}, steps={steps}; "
            f"end=(state {actual_state}, head {actual_head}), "
            f"expected=(state 3, head {target_head}), "
            f"first differing cells={differing[:30]}"
        )


def main() -> None:
    cases = 0

    # 144 cases: k=1..12, a=1..3, b=0..3, minimal valid L.
    for k in range(1, 13):
        n = 8 * k
        length = ceil(log2(n + 1))
        for a in range(1, 4):
            for b in range(4):
                check_case(k, a, b, length)
                cases += 1

    # 96 cases: vary the unused high-counter tail by taking L one or two
    # blocks larger than minimal.
    for k in range(1, 9):
        n = 8 * k
        minimum = ceil(log2(n + 1))
        for a in range(1, 3):
            for b in range(3):
                for extra in (1, 2):
                    check_case(k, a, b, minimum + extra)
                    cases += 1

    assert cases == 240
    print(f"PASS: {cases} deterministic TM63 reset-prefix simulations")


if __name__ == "__main__":
    main()
