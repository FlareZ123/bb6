#!/usr/bin/env python3
"""Independent exact finite-support check of the marker-1 even-L q4 macro.

This is computational evidence only.  It checks the full tape at every q4/0
checkpoint, all five q4 event heads in each cycle, and the exact step costs.
The transition table and initial tape are copied from the repository's TM2 /
S0 encoder conventions.
"""
from __future__ import annotations

import argparse
import json

# (write_bit, move, next_state); None denotes the unique halting query.
TRANSITIONS = {
    (0, 0): (1, 1, 1),
    (0, 1): None,
    (1, 0): (1, -1, 2),
    (1, 1): (0, 1, 5),
    (2, 0): (1, 1, 4),
    (2, 1): (0, -1, 3),
    (3, 0): (0, -1, 2),
    (3, 1): (1, 1, 1),
    (4, 0): (1, 1, 0),
    (4, 1): (1, 1, 4),
    (5, 0): (1, 1, 4),
    (5, 1): (0, 1, 3),
}

LH = [1, 1, 0, 1, 1, 1]
RIGHT0 = [0, 1, 1, 1, 0, 0, 1, 1, 1]


def bin_dec(width: int, n: int) -> list[int]:
    """S1Encoder.binaryCounterFuel width n, expanded into d0/d1 triples."""
    p = 2 ** (width + 1) - 1 - n
    out: list[int] = []
    for _ in range(width):
        if p <= 1:
            break
        out.extend([0, 0, 1] if p % 2 == 0 else [1, 1, 1])
        p //= 2
    return out


def v2(n: int) -> int:
    assert n > 0
    result = 0
    while n % 2 == 0:
        result += 1
        n //= 2
    return result


def initial_tape(a: int, length: int) -> set[int]:
    # s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 0 0
    left = [1] * (3 * a) + [1, 0, 1] + [0, 0, 1] + [1] * (3 * length) + LH
    tape = {-i for i, bit in enumerate(left) if bit}
    tape.update(i + 1 for i, bit in enumerate(RIGHT0) if bit)
    return tape


def step(state: int, head: int, tape: set[int]):
    bit = int(head in tape)
    transition = TRANSITIONS[(state, bit)]
    if transition is None:
        return None
    write, move, next_state = transition
    if write:
        tape.add(head)
    else:
        tape.discard(head)
    return next_state, head + move


def simulate(a: int, length: int, max_steps: int = 100_000_000) -> dict:
    assert a >= 1 and length >= 2 and length % 2 == 0
    m = 2**a * (2 ** (length + 2) - 1)
    width = a + length + 2
    tape = initial_tape(a, length)
    state, head = 3, 0
    events: list[tuple[int, int, int]] = []
    starts: list[tuple[int, set[int]]] = []

    for elapsed in range(max_steps):
        bit = int(head in tape)
        if state == 4 and bit == 0:
            events.append((elapsed, head, int(head + 1 in tape)))
            if head == 1:
                j = len(starts) + 1
                starts.append((elapsed, set(tape)))
                left = [0, 1, 1] + bin_dec(width, m - j) + LH
                right = [0, 0, 0] + [1] * (5 * j) + [0, 0, 1, 1, 1]
                expected = {
                    1 - i for i, value in enumerate(left) if value
                } | {
                    2 + i for i, value in enumerate(right) if value
                }
                if expected != tape:
                    raise AssertionError({
                        "failure": "checkpoint tape mismatch",
                        "a": a, "L": length, "j": j, "elapsed": elapsed,
                        "missing": sorted(expected - tape)[:20],
                        "extra": sorted(tape - expected)[:20],
                    })

        result = step(state, head, tape)
        if result is None:
            total_steps = elapsed
            break
        state, head = result
    else:
        raise TimeoutError(f"did not halt within {max_steps} steps: A={a}, L={length}")

    if len(starts) != m:
        raise AssertionError(("checkpoint count", len(starts), m))
    if len(events) != 7 + 5 * m:
        raise AssertionError(("q4 event count", len(events), 7 + 5 * m))

    for j in range(1, m):
        r = v2(m - j)
        first = 7 + 5 * (j - 1)
        got = [events[first + offset][1] for offset in range(5)]
        expected = [
            1,
            -(3 * r + 2),
            5 * (j + 1),
            5 * (j + 1) + 3,
            5 * (j + 1) + 7,
        ]
        if got != expected:
            raise AssertionError(("ordinary event heads", a, length, j, got, expected))
        cost = starts[j][0] - starts[j - 1][0]
        expected_cost = 20 * (j + 1) + 46 + 12 * r
        if cost != expected_cost:
            raise AssertionError(("ordinary cycle cost", a, length, j, cost, expected_cost))

    terminal_first = 7 + 5 * (m - 1)
    terminal_heads = [events[terminal_first + offset][1] for offset in range(5)]
    expected_terminal_heads = [
        1,
        -(3 * (a + length + 4) + 2),
        -(3 * (a + length + 3) + 1),
        2,
        5 * m + 6,
    ]
    if terminal_heads != expected_terminal_heads:
        raise AssertionError(("terminal heads", a, length, terminal_heads, expected_terminal_heads))

    prefix = starts[0][0]
    if prefix != 107 + 12 * (a + length):
        raise AssertionError(("prefix cost", prefix, 107 + 12 * (a + length)))
    terminal_cost = total_steps - starts[-1][0]
    expected_terminal_cost = 5 * m + 12 * (a + length) + 76
    if terminal_cost != expected_terminal_cost:
        raise AssertionError(("terminal cost", terminal_cost, expected_terminal_cost))

    expected_steps = 10 * m * m + 73 * m + 93 + 12 * (a + length)
    if total_steps != expected_steps:
        raise AssertionError(("total steps", total_steps, expected_steps))

    return {
        "A": a,
        "L": length,
        "M": m,
        "q4_checkpoints": len(starts),
        "q4_zero_events": len(events),
        "prefix_steps": prefix,
        "ordinary_cycles": m - 1,
        "terminal_cycle_steps": terminal_cost,
        "total_steps": total_steps,
        "terminal_event_heads": terminal_heads,
        "full_checkpoint_tapes_checked": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", default="1:2,2:2,3:2,1:4,2:4,1:6")
    parser.add_argument("--max-steps", type=int, default=100_000_000)
    args = parser.parse_args()
    results = []
    for case in args.cases.split(","):
        a, length = map(int, case.split(":"))
        results.append(simulate(a, length, args.max_steps))
    print(json.dumps({"status": "PASS", "cases": results}, indent=2))


if __name__ == "__main__":
    main()
