#!/usr/bin/env python3
"""Finite M211 trace and bounded-window over-approximation experiment.

This is empirical diagnostic code only. A finite trace or failure of a local
abstraction to prove safety is not a nonhalting proof.
"""

from __future__ import annotations

import argparse
import json

# (write_bit, head_delta, next_state); None is the undefined F1 transition.
TRANSITIONS = (
    ((1, +1, 1), (1, -1, 1)),  # A0, A1
    ((1, +1, 2), (0, -1, 4)),  # B0, B1
    ((0, +1, 3), (0, +1, 5)),  # C0, C1
    ((1, -1, 3), (1, +1, 4)),  # D0, D1
    ((1, +1, 0), (0, -1, 0)),  # E0, E1
    ((1, +1, 3), None),        # F0, F1
)
STATE_NAMES = "ABCDEF"


def simulate(max_steps: int, event_limit: int = 40) -> dict:
    offset = max_steps + 2
    tape = bytearray(2 * max_steps + 5)
    head = offset
    state = 0
    lo = hi = offset
    ones = f0 = f1 = c1 = c1_right_one = 0
    events = []
    c1_runs = []
    current_run = None
    steps = 0
    halted = False

    for step in range(1, max_steps + 1):
        bit = tape[head]
        if state == 2 and bit == 1:
            c1 += 1
            right = tape[head + 1]
            if right:
                c1_right_one += 1
            if len(events) < event_limit:
                events.append({
                    "step": step,
                    "head": head - offset,
                    "left": tape[head - 1],
                    "current": bit,
                    "right": right,
                    "window_head_minus_8_to_plus_12":
                        "".join(map(str, tape[head - 8 : head + 13])),
                })
            if current_run is not None and head - offset == current_run["end_head"] + 1:
                current_run["end_step"] = step
                current_run["end_head"] = head - offset
                current_run["length"] += 1
            else:
                if current_run is not None:
                    c1_runs.append(current_run)
                current_run = {
                    "start_step": step,
                    "end_step": step,
                    "start_head": head - offset,
                    "end_head": head - offset,
                    "length": 1,
                }
        if state == 5:
            if bit == 0:
                f0 += 1
            else:
                f1 += 1
                halted = True
                steps = step - 1
                break

        transition = TRANSITIONS[state][bit]
        if transition is None:
            halted = True
            steps = step - 1
            break
        write, delta, next_state = transition
        if bit != write:
            tape[head] = write
            ones += 1 if write else -1
        head += delta
        state = next_state
        lo = min(lo, head)
        hi = max(hi, head)
        steps = step

    if current_run is not None:
        c1_runs.append(current_run)
    histogram = {}
    for run in c1_runs:
        histogram[str(run["length"])] = histogram.get(str(run["length"]), 0) + 1
    for index, run in enumerate(c1_runs[:-1]):
        run["next_run_start_gap"] = c1_runs[index + 1]["start_step"] - run["end_step"]

    return {
        "steps_executed": steps,
        "halted": halted,
        "state": STATE_NAMES[state],
        "head": head - offset,
        "min_head": lo - offset,
        "max_head": hi - offset,
        "ones": ones,
        "F0_visits": f0,
        "F1_visits": f1,
        "C1_visits": c1,
        "C1_with_right_neighbor_1": c1_right_one,
        "C1_monotone_right_sweep_count": len(c1_runs),
        "C1_sweep_length_histogram": histogram,
        "first_C1_events": events,
        "first_C1_sweeps": c1_runs[:40],
    }


def local_window_bfs(radius: int) -> dict:
    """Over-approximate all tape windows of length 2r+1 around the head.

    After a move, the newly exposed far-edge cell is nondeterministically 0
    or 1. If F1 is reachable here, this abstraction is too coarse; this is
    not evidence that the concrete machine reaches F1.
    """
    length = 2 * radius + 1
    modulus = 1 << length
    mask = modulus - 1
    start = 0  # state A, all-zero local window
    seen = {start}
    queue = [start]
    cursor = 0
    bad = None

    while cursor < len(queue):
        code = queue[cursor]
        cursor += 1
        state, bits = divmod(code, modulus)
        current = (bits >> radius) & 1

        if state == 5 and current == 1:
            bad = {"state": "F", "bits": bits}
            break

        transition = TRANSITIONS[state][current]
        if transition is None:
            continue
        write, delta, next_state = transition
        written = (bits & ~(1 << radius)) | (write << radius)
        if delta == +1:
            base = (written >> 1) & mask
            next_windows = (base, base | (1 << (length - 1)))
        else:
            base = (written << 1) & mask
            next_windows = (base, base | 1)

        for next_bits in next_windows:
            next_code = next_state * modulus + next_bits
            if next_code not in seen:
                seen.add(next_code)
                queue.append(next_code)

    return {
        "radius": radius,
        "window_length": length,
        "reachable_abstract_states": len(seen),
        "F1_abstractly_reachable": bad is not None,
        "bad_abstract_state": bad,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=2_000_000)
    parser.add_argument("--max-radius", type=int, default=9)
    args = parser.parse_args()
    print(json.dumps({
        "table": "1RB1LB_1RC0LE_0RD0RF_1LD1RE_1RA0LA_1RD---",
        "finite_trace": simulate(args.steps),
        "local_window_overapproximations": [
            local_window_bfs(r) for r in range(1, args.max_radius + 1)
        ],
        "warning": "finite simulation and local abstraction are not proofs",
    }, indent=2))


if __name__ == "__main__":
    main()
