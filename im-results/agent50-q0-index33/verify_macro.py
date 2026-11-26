#!/usr/bin/env python3
"""Reproduce the q0 sibling-scan index-33 macro recurrence.

The residual table is the 11-transition partial machine
  1RB1RD1RC0RE0LA---1LA1LD0LF0RB1LF0LC
with the sole undefined slot C1. This script starts at the proposed
canonical F1 checkpoints and checks every transition to the next checkpoint.
It is computational evidence, not a proof of nonhalting.
"""
from collections import defaultdict

# State indices A..F; transition = (write, direction, next_state).
# direction +1 = R, -1 = L. C1 is intentionally absent (halt).
M = {
    (0, 0): (1, +1, 1),  # A0 = 1RB
    (0, 1): (1, +1, 3),  # A1 = 1RD
    (1, 0): (1, +1, 2),  # B0 = 1RC
    (1, 1): (0, +1, 4),  # B1 = 0RE
    (2, 0): (0, -1, 0),  # C0 = 0LA
    (3, 0): (1, -1, 0),  # D0 = 1LA
    (3, 1): (1, -1, 3),  # D1 = 1LD
    (4, 0): (0, -1, 5),  # E0 = 0LF
    (4, 1): (0, +1, 1),  # E1 = 0RB
    (5, 0): (1, -1, 5),  # F0 = 1LF
    (5, 1): (0, -1, 2),  # F1 = 0LC
}
NAMES = "ABCDEF"


def canonical(k: int, j: int):
    """S(k,j): F at the left edge of a 4j-one block, plus a left singleton."""
    assert 1 <= j <= k
    left_marker = -2 * k
    block_left = 2 * k + 3 - 4 * j
    block_right = 2 * k + 2
    tape = {left_marker: 1}
    tape.update((x, 1) for x in range(block_left, block_right + 1))
    return 5, block_left, tape


def runs(tape):
    xs = sorted(x for x, bit in tape.items() if bit)
    out = []
    for x in xs:
        if not out or x > out[-1][1] + 1:
            out.append([x, x])
        else:
            out[-1][1] = x
    return tuple((a, b) for a, b in out)


def macro(k: int, j: int):
    state, head, tape = canonical(k, j)
    if j < k:
        k2, j2 = k, j + 1
        expected_steps = 8 * j + 20
    else:
        k2, j2 = k + 1, 1
        expected_steps = 4 * k + 34
    expected = canonical(k2, j2)
    for step in range(1, expected_steps + 1):
        symbol = tape.get(head, 0)
        tr = M.get((state, symbol))
        if tr is None:
            raise AssertionError(
                f"unexpected C1 halt in S({k},{j}) at local step {step}, "
                f"head={head}, tape-runs={runs(tape)}"
            )
        write, direction, next_state = tr
        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        head += direction
        state = next_state
        if step < expected_steps and state == 5 and tape.get(head, 0) == 1:
            raise AssertionError(f"non-first F1 return in S({k},{j}) at local step {step}")
    actual = (state, head, tape)
    if actual != expected:
        raise AssertionError(
            f"S({k},{j}) macro mismatch after {expected_steps} steps\n"
            f"actual state/head/runs: {NAMES[state]} {head} {runs(tape)}\n"
            f"expected state/head/runs: {NAMES[expected[0]]} {expected[1]} {runs(expected[2])}"
        )
    return expected_steps


def blank_seed():
    state, head, tape = 0, 0, {}
    for step in range(1, 32):
        symbol = tape.get(head, 0)
        tr = M.get((state, symbol))
        if tr is None:
            raise AssertionError(f"unexpected blank-run halt at step {step}")
        write, direction, next_state = tr
        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        head += direction
        state = next_state
    if (state, head, tape) != canonical(1, 1):
        raise AssertionError(f"blank seed mismatch: {state=} {head=} {runs(tape)=}")


def main(max_k=100):
    blank_seed()
    total = 0
    macros = 0
    for k in range(1, max_k + 1):
        for j in range(1, k + 1):
            total += macro(k, j)
            macros += 1
    print("verified blank run reaches S(1,1) after 31 steps")
    print(f"verified {macros} macro transitions for 1 <= j <= k <= {max_k}")
    print(f"total simulated transitions: {total}")
    print("j<k: S(k,j) -> S(k,j+1) in 8*j+20 steps")
    print("j=k: S(k,k) -> S(k+1,1) in 4*k+34 steps")


if __name__ == "__main__":
    main()
