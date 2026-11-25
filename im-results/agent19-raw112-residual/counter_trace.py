#!/usr/bin/env python3
"""Reproduce the C-boundary counter trace for raw112 residual 0LE.

The simulator is deliberately small and independent of Lean.  Its output is
empirical discovery data only; it is not itself a nonhalting proof.
"""
from __future__ import annotations

import argparse
import csv
from pathlib import Path

TABLE = (
    (("1", "R", 1), ("0", "R", 5)),  # A
    (("1", "R", 2), ("0", "L", 1)),  # B
    (("0", "R", 3), ("0", "L", 1)),  # C
    (("1", "L", 3), ("1", "R", 4)),  # D
    (("0", "R", 0), ("1", "L", 2)),  # E
    (None,           ("0", "L", 4)),  # F; F0 is undefined
)
STATE_NAMES = "ABCDEF"
PUMP_BLOCK = "110000"

# Observed recursive base-6 encoding of the five-bit high-counter blocks.
BASE_HIGH = {
    0: [],
    1: ["11111"],
    2: ["00001", "11111"],
    3: ["11100", "00001", "11111"],
    4: ["00111", "11101", "11111"],
    5: ["11111", "11101", "11111"],
}
HIGH_PREFIX = {
    (0, 0): ["00000", "00000", "00000"],
    (0, 1): ["00000", "00110", "00001"],
    (1, 0): ["11111", "00000", "00000"],
    (1, 1): ["11111", "00110", "00001"],
    (2, 0): ["00001", "11111", "00000"],
    (2, 1): ["00001", "11110", "00001"],
    (3, 0): ["11100", "00001", "11111"],
    (3, 1): ["11100", "00011", "11111"],
    (4, 0): ["00111", "11101", "11111"],
    (4, 1): ["00111", "11111", "11111"],
    (5, 0): ["11111", "11101", "11111"],
    (5, 1): ["11111", "11111", "11111"],
}


def encode_high(k: int) -> list[str]:
    if k < 6:
        return BASE_HIGH[k]
    quotient, residue = divmod(k, 6)
    return HIGH_PREFIX[residue, quotient % 2] + encode_high(quotient)



def bits_near_to_far(word: int) -> str:
    return "".join("1" if (word >> i) & 1 else "0"
                   for i in range(word.bit_length()))


def trace(max_steps: int):
    # L and R are little-endian integers: bit 0 is the cell nearest the head.
    # This is the same compact zipper representation used by the original
    # simulator, and avoids scanning the full nonblank tape at every step.
    left = 0
    right = 0
    bit = 0
    head_state = 0
    seen: set[int] = set()
    records = []
    halted = None

    for step in range(1, max_steps + 1):
        tr = TABLE[head_state][bit]
        if tr is None:
            halted = (step - 1, head_state, bit)
            break

        write, direction, next_state = tr
        written = int(write == "1")
        if direction == "R":
            next_bit = right & 1
            left = (left << 1) | written
            right >>= 1
        else:
            next_bit = left & 1
            right = (right << 1) | written
            left >>= 1
        head_state = next_state
        bit = next_bit

        # Canonical C-boundary configuration: current 0, left word exactly 1.
        if head_state != 2 or bit != 0 or left != 1:
            continue

        right_word = bits_near_to_far(right)
        if not right_word.startswith("00"):
            continue

        pos = 2
        n = 0
        while right_word[pos:pos + len(PUMP_BLOCK)] == PUMP_BLOCK:
            n += 1
            pos += len(PUMP_BLOCK)
        if n < 1 or n in seen:
            continue

        suffix = right_word[pos:]
        if not suffix.startswith("001111") or len(suffix) < 18:
            continue
        low = suffix[6:18]
        high = suffix[18:]
        if len(high) % 5:
            continue
        blocks = [high[i:i + 5] for i in range(0, len(high), 5)]
        seen.add(n)
        records.append({
            "n": n,
            "step": step,
            "state": STATE_NAMES[head_state],
            "left": "1",
            "right_prefix": "00" + PUMP_BLOCK * n,
            "suffix": suffix,
            "low_code": low,
            "high_blocks": " ".join(blocks),
            "high_block_count": len(blocks),
            "suffix_length": len(suffix),
        })

    return records, halted


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=10_000_000)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).with_name("counter-trace.csv"))
    parser.add_argument("--high-out", type=Path,
                        default=Path(__file__).with_name("high-counter.csv"))
    args = parser.parse_args()

    records, halted = trace(args.steps)
    low_by_residue = {}
    high_by_quotient = {}
    for row in records:
        residue = row["n"] % 6
        quotient = row["n"] // 3
        low = row["low_code"]
        high = row["high_blocks"]
        if residue in low_by_residue and low_by_residue[residue] != low:
            raise AssertionError(f"low code depends on more than n mod 6: n={row['n']}")
        if quotient in high_by_quotient and high_by_quotient[quotient] != high:
            raise AssertionError(f"high code depends on more than floor(n/3): n={row['n']}")
        expected = " ".join(encode_high(quotient))
        if high != expected:
            raise AssertionError(
                f"base-6 high-code recurrence mismatch at k={quotient}: "
                f"observed={high!r}, expected={expected!r}"
            )
        low_by_residue[residue] = low
        high_by_quotient[quotient] = high

    args.out.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "n", "step", "state", "left", "right_prefix", "suffix",
        "low_code", "high_blocks", "high_block_count", "suffix_length",
    ]
    with args.out.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(records)

    high_rows = []
    by_n = {row["n"]: row for row in records}
    for quotient, blocks in sorted(high_by_quotient.items()):
        n = 3 * quotient + 1
        row = by_n.get(n)
        if row is None:
            row = next(x for x in records if x["n"] // 3 == quotient)
        high_rows.append({
            "quotient": quotient,
            "representative_n": row["n"],
            "step": row["step"],
            "blocks": blocks,
            "block_count": 0 if not blocks else len(blocks.split()),
        })
    with args.high_out.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=[
            "quotient", "representative_n", "step", "blocks", "block_count"
        ])
        writer.writeheader()
        writer.writerows(high_rows)

    print(f"steps={args.steps} canonical_configs={len(records)} "
          f"max_n={max((r['n'] for r in records), default=0)}")
    print(f"low_code_residues={len(low_by_residue)} "
          f"high_counter_states={len(high_by_quotient)}")
    print(f"csv={args.out}")
    print(f"high_csv={args.high_out}")
    print(f"undefined_transition={halted}")


if __name__ == "__main__":
    main()
