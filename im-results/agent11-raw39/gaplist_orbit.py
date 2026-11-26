#!/usr/bin/env python3
"""Reproduce the Raw39 1LE F1-sibling gap-list boundary orbit.

This is an experimental simulator, not a proof of nonhalting.  It starts from
the observed F0 boundary with left tape 00 and right gap blocks 0^g11.
"""
import argparse
import json

# State order A,B,C,D,E,F.  Direction 1 is R; direction 0 is L.
BASE = [
    [(1, 1, 1), (1, 0, 4)],   # A
    [(1, 1, 2), (0, 0, 4)],   # B
    [(0, 1, 3), None],        # C
    [(1, 0, 3), (0, 1, 0)],   # D
    [(0, 0, 1), (0, 1, 5)],   # E
    [(1, 1, 4), None],        # F
]
F1 = {
    5777: (0, 1, 2),  # 0RC
    5779: (0, 1, 4),  # 0RE
    5787: (1, 1, 2),  # 1RC
}


def table_for(variant):
    table = [row[:] for row in BASE]
    table[5][1] = F1[variant]
    return table


def encode_gaps(gaps):
    out = []
    for gap in gaps:
        if gap < 0:
            raise ValueError("negative gap")
        out.extend([0] * gap)
        out.extend([1, 1])
    return out


def decode_gaps(bits):
    """Decode 0^g11 blocks, ignoring only trailing blank zeros."""
    bits = list(bits)
    while bits and bits[-1] == 0:
        bits.pop()
    gaps = []
    i = 0
    while i < len(bits):
        gap = 0
        while i < len(bits) and bits[i] == 0:
            gap += 1
            i += 1
        if i + 2 > len(bits) or bits[i:i + 2] != [1, 1]:
            raise ValueError("right tape is not a concatenation of 0^g11 blocks")
        gaps.append(gap)
        i += 2
    return gaps


def run_phase(table, prefix_in, prefix_out, tail, max_steps):
    """Run from F0/left=00/prefix_in++tail to the next F0/left=00 boundary."""
    left = [0]  # nearest-first; together with current 0 this is exactly 00
    right = list(reversed(encode_gaps(prefix_in + tail)))  # nearest-first
    current = 0
    state = 5  # F
    steps = 0
    f1_visits = 0

    while steps <= max_steps:
        if steps and state == 5 and current == 0 and left == [0]:
            gaps = decode_gaps(reversed(right))
            if gaps[:len(prefix_out)] != prefix_out:
                raise RuntimeError(
                    f"unexpected F0 boundary prefix {gaps[:len(prefix_out)]}; "
                    f"expected {prefix_out}"
                )
            return gaps[len(prefix_out):], steps, f1_visits

        if state == 5 and current == 1:
            f1_visits += 1
        action = table[state][current]
        if action is None:
            raise RuntimeError(
                f"halted at step {steps}, state {state}, symbol {current}"
            )
        write, direction, next_state = action
        current = write
        if direction == 1:
            left.append(current)
            current = right.pop() if right else 0
        else:
            right.append(current)
            current = left.pop() if left else 0
        state = next_state
        steps += 1

    raise TimeoutError(f"no target boundary within {max_steps} steps")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--iterations", type=int, default=20)
    parser.add_argument("--max-steps", type=int, default=2_000_000)
    args = parser.parse_args()

    variants = (5777, 5779, 5787)
    W = [1]
    for i in range(args.iterations):
        rows = {}
        outputs = {}
        for variant in variants:
            table = table_for(variant)
            unchanged, p_steps, p_f1 = run_phase(
                table, [1, 5], [3, 1, 2], W, args.max_steps
            )
            if unchanged != W:
                raise AssertionError(f"phase P changed the tail for {variant}")
            next_W, q_steps, q_f1 = run_phase(
                table, [3, 1, 2], [1, 5], W, args.max_steps
            )
            outputs[variant] = next_W
            rows[str(variant)] = {
                "phase_P_steps": p_steps,
                "phase_P_F1_visits": p_f1,
                "phase_Q_steps": q_steps,
                "phase_Q_F1_visits": q_f1,
                "output_W": next_W,
            }

        distinct = {tuple(v) for v in outputs.values()}
        if len(distinct) != 1:
            raise AssertionError(f"variant outputs diverged: {outputs}")
        W_next = outputs[5777]
        record = {
            "iteration": i,
            "input_W": W,
            "input_length": len(W),
            "input_gap_sum": sum(W),
            "variants": rows,
            "common_output_W": W_next,
            "output_length": len(W_next),
            "output_gap_sum": sum(W_next),
            "encoded_output_tape_length": sum(g + 2 for g in [1, 5] + W_next),
        }
        print(json.dumps(record, separators=(",", ":")))
        W = W_next


if __name__ == "__main__":
    main()
