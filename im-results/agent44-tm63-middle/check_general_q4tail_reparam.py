#!/usr/bin/env python3
"""Small exact-TM2 sanity checks for the arbitrary-A q4Tail S1 reparameterization.

This checks (1) equality of the q4Tail S0 adapter tape and the proposed S1
configuration at time zero, and (2) the exact counted-drain endpoint for the
closed-form drain cost. It does NOT simulate or prove the full SectionResult
dispatcher and is not a halting proof.

Run with: python3 check_general_q4tail_reparam.py
"""

from itertools import product

D0 = [0, 0, 1]
D1 = [1, 1, 1]
LH = [1, 1, 0, 1, 1, 1]

# State/symbol -> (write, move, next state); None is the halt transition.
# Copied from the repository's TM2 definition in ChampionRootBridge.lean.
TM2 = [
    [(1, 1, 1), None],
    [(1, -1, 2), (0, 1, 5)],
    [(1, 1, 4), (0, -1, 3)],
    [(0, -1, 2), (1, 1, 1)],
    [(1, 1, 0), (1, 1, 4)],
    [(1, 1, 4), (0, 1, 3)],
]


def repeat_block(block, count):
    return block * count


def bin_dec(width, value):
    if width == 0:
        return []
    block = D1 if value % 2 == 0 else D0
    return block + bin_dec(width - 1, value // 2)


def right_facing(counter):
    # s0RightFacing(counter): fixed separator followed by d1pow(counter+1).
    return [0, 1, 1, 1, 0, 0] + repeat_block(D1, counter + 1)


def tape_from(head, left, right):
    tape = {}
    for i, bit in enumerate(left):
        if bit:
            tape[head - i] = 1
    for i, bit in enumerate(right):
        if bit:
            tape[head + 1 + i] = 1
    return tape


def same_tape(left, right):
    return left == right


def drain_cost_for_power_of_two_minus_one(exponent):
    # drainCost (2^exponent - 1) 0, from m0_even_n2_replay.py.
    return 6 * 4**exponent + 42 * 2**exponent - 12 * exponent - 48


def run_steps(state, head, tape, steps):
    tape = dict(tape)
    for step in range(steps):
        transition = TM2[state][tape.get(head, 0)]
        if transition is None:
            return None, state, head, tape, step
        write, move, next_state = transition
        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        head += move
        state = next_state
    return True, state, head, tape, steps


def check_case(L, A, z):
    w = A + L + 1
    q = 2 ** (A - 1) * (2 ** (L + 2) - 1) - 1
    M = 2**A * (2 ** (L + 2) - 1)
    W = A + L + 2
    N = M - 3

    K = 2**z + z + 3
    m = 3 * 2**z + 3 * z + 7
    n = 2 ** (2**z - 1)
    H = m + 2 + 3 * n
    right_counter = 2 ** (n - 1) - 1
    unary_width = K + n - 1

    tail0 = [1] * 4 + bin_dec(w, q) + LH
    tail = [1, 0, 0, 1, 1, 1] + tail0[6:]
    residual = [1] * (m + 2) + [0, 1, 0, 0] + tail

    # Authentic q4Tail adapter endpoint, represented as an S0 tape.
    s0_left = bin_dec(n - 1, right_counter) + residual
    s0_tape = tape_from(H, s0_left, right_facing(0))

    # Proposed S1 representation at the same head and with the same right
    # counter. markerWord(0)=[0,1], followed by d0 and the outer BinDec.
    s1_left = (
        bin_dec(unary_width, right_counter)
        + [0, 1]
        + D0
        + bin_dec(W, N)
        + LH
    )
    s1_tape = tape_from(H, s1_left, right_facing(0))
    start_equal = same_tape(s0_tape, s1_tape)

    # Counted drain: move the left counter to the right counter.
    drain_steps = drain_cost_for_power_of_two_minus_one(n - 1)
    halted, final_state, final_head, final_tape, executed = run_steps(
        3, H, s0_tape, drain_steps
    )

    expected_final_left = (
        bin_dec(unary_width, 0) + [0, 1] + D0 + bin_dec(W, N) + LH
    )
    expected_final_tape = tape_from(
        H, expected_final_left, right_facing(right_counter)
    )
    drain_equal = (
        halted is True
        and final_state == 3
        and final_head == H
        and same_tape(final_tape, expected_final_tape)
    )

    assert N % 3 == 0, (L, A, N)
    assert start_equal, (L, A, z, "S0/S1 start mismatch")
    assert drain_equal, (L, A, z, "counted drain mismatch")

    return {
        "L": L,
        "A": A,
        "z": z,
        "W": W,
        "N_mod_3": N % 3,
        "unary_width": unary_width,
        "drain_steps": drain_steps,
        "S0_equals_S1": start_equal,
        "drain_endpoint_matches": drain_equal,
    }


def main():
    rows = [
        check_case(L, A, z)
        for L, A, z in product((4, 6, 76), (2, 3, 4), (1, 2))
    ]
    print(f"PASS: {len(rows)} parameter triples")
    for row in rows:
        print(row)


if __name__ == "__main__":
    main()
