#!/usr/bin/env python3
"""Check the generalized marker-1 q4 checkpoint left-frame invariant.

For S0 input s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A z 0,
this checks the first `max_checkpoints` occurrences of state 4 at head 1.
It verifies the entire left-facing finite-support word and records (but does
not conjecturally normalize) the right-facing word.  No halting claim is made.
"""
from __future__ import annotations
import argparse
import json

TRANSITIONS = {
    (0, 0): (1, 1, 1), (0, 1): None,
    (1, 0): (1, -1, 2), (1, 1): (0, 1, 5),
    (2, 0): (1, 1, 4), (2, 1): (0, -1, 3),
    (3, 0): (0, -1, 2), (3, 1): (1, 1, 1),
    (4, 0): (1, 1, 0), (4, 1): (1, 1, 4),
    (5, 0): (1, 1, 4), (5, 1): (0, 1, 3),
}
LH = [1, 1, 0, 1, 1, 1]
RIGHT0 = [0, 1, 1, 1, 0, 0, 1, 1, 1]


def bin_dec(width: int, n: int) -> list[int]:
    p = 2 ** (width + 1) - 1 - n
    out: list[int] = []
    for _ in range(width):
        if p <= 1:
            break
        out.extend([0, 0, 1] if p % 2 == 0 else [1, 1, 1])
        p //= 2
    return out


def initial_tape(a: int, length: int, z: int) -> set[int]:
    left = bin_dec(a, z) + [1, 0, 1] + [0, 0, 1] + [1] * (3 * length) + LH
    tape = {-i for i, bit in enumerate(left) if bit}
    tape.update(i + 1 for i, bit in enumerate(RIGHT0) if bit)
    return tape


def rle(bits: list[int]) -> list[list[int]]:
    if not bits:
        return []
    runs: list[list[int]] = []
    current, count = bits[0], 0
    for bit in bits:
        if bit == current:
            count += 1
        else:
            runs.append([current, count])
            current, count = bit, 1
    runs.append([current, count])
    return runs


def simulate_prefix(a: int, length: int, z: int, max_checkpoints: int,
                    max_steps: int, right_window: int) -> dict:
    assert a >= 1 and length >= 2 and length % 2 == 0
    assert 0 <= z < 2**a
    m = 2**a * (2 ** (length + 2) - 1)
    width = a + length + 2
    tape = initial_tape(a, length, z)
    state, head = 3, 0
    checkpoints: list[dict] = []
    q4_events = 0

    for elapsed in range(max_steps):
        bit = int(head in tape)
        if state == 4 and bit == 0:
            q4_events += 1
            if head == 1:
                j = len(checkpoints) + 1
                left = [0, 1, 1] + bin_dec(width, m - j) + LH
                expected_left = {1 - i for i, value in enumerate(left) if value}
                actual_left = {position for position in tape if position <= 1}
                if expected_left != actual_left:
                    raise AssertionError({
                        "failure": "left checkpoint frame mismatch", "A": a, "L": length,
                        "z": z, "j": j, "elapsed": elapsed,
                        "missing": sorted(expected_left - actual_left)[:30],
                        "extra": sorted(actual_left - expected_left)[:30],
                    })
                right_bits = [int(2 + i in tape) for i in range(right_window)]
                if len(right_bits) >= 3 and right_bits[:3] != [0, 0, 0]:
                    raise AssertionError(("right checkpoint prefix", a, length, z, j, right_bits[:3]))
                if z == 0:
                    expected_right = [0, 0, 0] + [1] * (5 * j) + [0, 0, 1, 1, 1]
                    actual_right = [int(2 + i in tape) for i in range(len(expected_right))]
                    if actual_right != expected_right:
                        raise AssertionError(("z=0 right frame mismatch", j, actual_right, expected_right))
                checkpoints.append({
                    "j": j,
                    "step": elapsed,
                    "q4_event_index": q4_events,
                    "left_word": "".join(map(str, left)),
                    "right_window_rle": rle(right_bits),
                })
                if len(checkpoints) >= max_checkpoints:
                    return {
                        "status": "PASS_CHECKPOINT_PREFIX",
                        "A": a, "L": length, "z": z, "M": m,
                        "checkpoints": checkpoints,
                        "halted": False,
                    }

        transition = TRANSITIONS[(state, bit)]
        if transition is None:
            return {
                "status": "HALTED_BEFORE_LIMIT",
                "A": a, "L": length, "z": z, "M": m,
                "checkpoints": checkpoints,
                "q4_zero_events_seen": q4_events,
                "halted": True,
                "total_steps": elapsed,
            }
        write, move, next_state = transition
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        state, head = next_state, head + move

    return {
        "status": "STEP_LIMIT",
        "A": a, "L": length, "z": z, "M": m,
        "checkpoints": checkpoints,
        "q4_zero_events_seen": q4_events,
        "halted": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", default="1:2:0,4:2:1,3:2:2")
    parser.add_argument("--max-checkpoints", type=int, default=3)
    parser.add_argument("--max-steps", type=int, default=2_000_000)
    parser.add_argument("--right-window", type=int, default=80)
    args = parser.parse_args()
    results = []
    for case in args.cases.split(","):
        a, length, z = map(int, case.split(":"))
        results.append(simulate_prefix(a, length, z, args.max_checkpoints,
                                       args.max_steps, args.right_window))
    print(json.dumps({"cases": results}, indent=2))


if __name__ == "__main__":
    main()
