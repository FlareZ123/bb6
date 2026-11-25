#!/usr/bin/env python3
"""Reproduce the canonical counter trace for the raw112 F1=1RB residual.

This is an untrusted discovery script. Its finite trace and grammar checks
are empirical only; they do not prove nonhalting or the macro transition.
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
    (None,           ("1", "R", 1)),  # F; F0 is undefined
)
STATE_NAMES = "ABCDEF"
PUMP_BLOCK = "110000"

LOW_CODES = {
    0: "110000000000",
    1: "000000111111",
    2: "111110111111",
    3: "110011000001",
    4: "000001111111",
    5: "111111111111",
}

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
    """Observed recursive base-6 encoding of the high five-bit stack."""
    if k < 6:
        return BASE_HIGH[k]
    quotient, residue = divmod(k, 6)
    return HIGH_PREFIX[residue, quotient % 2] + encode_high(quotient)


def recursive_carry_cost(k: int) -> int:
    """Observed recursive cost for the high-counter carry subroutine."""
    q, r = divmod(k, 6)
    if r == 0:
        return 326
    if r == 1:
        return 350 if q % 2 == 0 else 344
    if r == 2:
        return 378 if q % 2 == 0 else 372
    if r == 3:
        return 338
    if r == 4:
        return 320
    if q == 0:
        return 416
    if q == 1:
        return 440
    if q == 2:
        return 468
    return recursive_carry_cost(q) + 90


def observed_macro_cost(n: int) -> int:
    """Conjectured C(n)->C(n+1) cost, empirically checked by this script."""
    base = 144 * n
    r = n % 6
    if r == 0:
        return base + 312
    if r in (1, 4):
        return base + 242
    if r == 2 or r == 5:
        return base + recursive_carry_cost(n // 3)
    if r == 3:
        return base + 300
    raise AssertionError(r)


def bits_near_to_far(word: int) -> str:
    return "".join("1" if (word >> i) & 1 else "0"
                   for i in range(word.bit_length()))


def trace(max_steps: int):
    # Little-endian zipper: bit 0 is the cell nearest the head.
    left = 0
    right = 0
    bit = 0
    state = 0
    seen: set[int] = set()
    records = []
    undefined = None
    f_visits = 0
    a1_with_zero_right = 0

    for step in range(1, max_steps + 1):
        if state == 5:
            if bit == 0:
                undefined = (step - 1, state, bit)
                break
            f_visits += 1
        if state == 0 and bit == 1 and (right & 1) == 0:
            a1_with_zero_right += 1

        transition = TABLE[state][bit]
        if transition is None:
            undefined = (step - 1, state, bit)
            break

        write, direction, next_state = transition
        written = int(write == "1")
        if direction == "R":
            next_bit = right & 1
            left = (left << 1) | written
            right >>= 1
        else:
            next_bit = left & 1
            right = (right << 1) | written
            left >>= 1
        state = next_state
        bit = next_bit

        # Canonical C-boundary: current 0, left word exactly 1.
        if state != 2 or bit != 0 or left != 1:
            continue
        right_word = bits_near_to_far(right)
        if not right_word.startswith("00"):
            continue

        pos = 2
        n = 0
        while right_word[pos:pos + 6] == PUMP_BLOCK:
            n += 1
            pos += 6
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
        if low != LOW_CODES[n % 6]:
            raise AssertionError(f"low code mismatch at n={n}: {low}")
        expected_high = encode_high(n // 3)
        if blocks != expected_high:
            raise AssertionError(
                f"high stack mismatch at n={n}, k={n // 3}: "
                f"observed={blocks!r}, expected={expected_high!r}"
            )
        seen.add(n)
        records.append({
            "n": n,
            "step": step,
            "state": STATE_NAMES[state],
            "left": "1",
            "right_prefix": "00" + PUMP_BLOCK * n,
            "suffix": suffix,
            "low_code": low,
            "high_blocks": " ".join(blocks),
            "high_block_count": len(blocks),
            "suffix_length": len(suffix),
        })

    # Check the observed macro-cost recurrence between every adjacent pair.
    for i, row in enumerate(records[:-1]):
        actual = records[i + 1]["step"] - row["step"]
        predicted = observed_macro_cost(row["n"])
        if actual != predicted:
            raise AssertionError(
                f"macro cost mismatch at n={row['n']}: "
                f"observed={actual}, predicted={predicted}"
            )
        row["observed_macro_cost"] = actual
        row["predicted_macro_cost"] = predicted
    if records:
        records[-1]["observed_macro_cost"] = ""
        records[-1]["predicted_macro_cost"] = ""

    return records, undefined, f_visits, a1_with_zero_right


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=10_000_000)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).with_name("raw112-f1-1rb-trace.csv"))
    parser.add_argument("--high-out", type=Path,
                        default=Path(__file__).with_name("raw112-f1-1rb-high.csv"))
    args = parser.parse_args()

    records, undefined, f_visits, a1_bad = trace(args.steps)
    if undefined is not None:
        raise AssertionError(f"undefined transition reached: {undefined}")
    if a1_bad != 0:
        raise AssertionError(f"A/1 with zero to the right observed {a1_bad} times")
    by_n = {row["n"]: row for row in records}
    high_rows = []
    for k in sorted({n // 3 for n in by_n}):
        row = next(row for n, row in by_n.items() if n // 3 == k)
        blocks = encode_high(k)
        high_rows.append({
            "quotient": k,
            "representative_n": row["n"],
            "step": row["step"],
            "blocks": " ".join(blocks),
            "block_count": len(blocks),
        })

    args.out.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "n", "step", "state", "left", "right_prefix", "suffix",
        "low_code", "high_blocks", "high_block_count", "suffix_length",
    ]
    with args.out.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(records)

    with args.high_out.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=[
            "quotient", "representative_n", "step", "blocks", "block_count"
        ])
        writer.writeheader()
        writer.writerows(high_rows)

    print(f"steps={args.steps} canonical_configs={len(records)} "
          f"max_n={max((row['n'] for row in records), default=0)}")
    print(f"high_counter_states={len(high_rows)} F_visits={f_visits} "
          f"A1_with_zero_right={a1_bad}")
    print(f"macro_costs_checked={max(0, len(records) - 1)} "
          f"formula=144*n+phase_or_recursive_F")
    print(f"undefined_transition={undefined}")
    print(f"csv={args.out}")
    print(f"high_csv={args.high_out}")


if __name__ == "__main__":
    main()
