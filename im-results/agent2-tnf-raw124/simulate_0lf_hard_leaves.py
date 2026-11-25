#!/usr/bin/env python3
"""Reproducible sparse-tape traces for the five raw124/F1=0LF/F0=1RB residuals.

The two translation-invariant 64-bit hashes are candidate filters only. Every
hash repeat is checked by reconstructing both exact tapes and comparing their
sorted one-cell positions relative to the head. This is empirical simulation,
not a nonhalting proof.
"""
from __future__ import annotations
import argparse
import json
import time
from pathlib import Path

TABLES = [
    "1RB0LE_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF",
    "1RB---_1RC1RF_0RD0RB_1LD1RE_0RA1LF_1RB0LF",
    "1RB---_1RC1RF_0RD0RB_1LD1RE_1RA1LF_1RB0LF",
    "1RB---_1RC1RA_0RD0RE_1LD1RE_0RB1LF_1RB0LF",
    "1RB0RD_1RC---_0RD1LA_1LD1RE_1RB1LF_1RB0LF",
]
MASK = (1 << 64) - 1
BASES = (0x9E3779B185EBCA87, 0xC2B2AE3D27D4EB4F)
INVERSES = tuple(pow(base, -1, 1 << 64) for base in BASES)

def parse_table(code: str):
    raw = code.replace("_", "")
    if len(raw) != 36:
        raise ValueError(f"expected 36 transition characters: {code}")
    out = []
    for i in range(0, 36, 3):
        token = raw[i:i + 3]
        if token == "---":
            out.append(None)
        else:
            if token[0] not in "01" or token[1] not in "LR" or token[2] not in "ABCDEF":
                raise ValueError(f"invalid transition {token!r}")
            out.append((int(token[0]), token[1], ord(token[2]) - ord("A")))
    return out

def exact_snapshot(table, steps: int):
    ones = set()
    head = state = 0
    for _ in range(steps):
        bit = int(head in ones)
        move = table[2 * state + bit]
        if move is None:
            return {"ones": ones, "head": head, "state": -1}
        write, direction, next_state = move
        if write != bit:
            if write: ones.add(head)
            else: ones.remove(head)
        head += 1 if direction == "R" else -1
        state = next_state
    return {"ones": ones, "head": head, "state": state}

def simulate(table, steps: int) -> dict:
    ones = set()
    head = state = 0
    counts = [0] * 12
    first = [None] * 12
    minimum = maximum = 0
    hashes = [0, 0]
    seen = {}
    hash_repeats = 0
    for step in range(steps):
        bit = int(head in ones)
        index = 2 * state + bit
        move = table[index]
        if move is None:
            return {
                "kind": "hole", "halt_step": step + 1,
                "hole": {"state": "ABCDEF"[state], "symbol": bit},
                "counts": counts, "first_visit": first,
                "head": head, "ones": len(ones), "seen_hashes": len(seen),
                "hash_repeats": hash_repeats,
            }
        counts[index] += 1
        if first[index] is None: first[index] = step + 1
        write, direction, next_state = move
        if write != bit:
            delta = 1 if write else -1
            if write: ones.add(head)
            else: ones.remove(head)
            hashes[0] = (hashes[0] + delta) & MASK
            hashes[1] = (hashes[1] + delta) & MASK
        if direction == "R":
            head += 1
            hashes[0] = hashes[0] * INVERSES[0] & MASK
            hashes[1] = hashes[1] * INVERSES[1] & MASK
        else:
            head -= 1
            hashes[0] = hashes[0] * BASES[0] & MASK
            hashes[1] = hashes[1] * BASES[1] & MASK
        state = next_state
        minimum = min(minimum, head)
        maximum = max(maximum, head)
        key = (state, hashes[0], hashes[1], len(ones))
        previous = seen.get(key)
        if previous is None:
            seen[key] = step + 1
        else:
            hash_repeats += 1
            old = exact_snapshot(table, previous)
            current_relative = sorted(position - head for position in ones)
            old_relative = sorted(position - old["head"] for position in old["ones"])
            if old["state"] == state and current_relative == old_relative:
                return {
                    "kind": "translated-cycle",
                    "start_step": previous, "end_step": step + 1,
                    "period": step + 1 - previous, "translation": head - old["head"],
                    "state": "ABCDEF"[state], "relative_ones": current_relative,
                    "counts": counts, "first_visit": first,
                }
            seen[key] = step + 1
    return {
        "kind": "open", "steps": steps, "counts": counts, "first_visit": first,
        "head": head, "state": "ABCDEF"[state], "ones": len(ones),
        "min_head": minimum, "max_head": maximum, "span": maximum - minimum + 1,
        "seen_hashes": len(seen), "hash_repeats": hash_repeats,
        "translation_hashes": [f"{h:016x}" for h in hashes],
    }

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=1_000_000)
    parser.add_argument("--output", type=Path, default=Path("0lf-hard-simulation.json"))
    args = parser.parse_args()
    if args.steps < 1: parser.error("--steps must be positive")
    started = time.perf_counter()
    results = []
    for index, code in enumerate(TABLES):
        results.append({"leaf": index, "table": code, **simulate(parse_table(code), args.steps)})
    output = {"steps_per_table": args.steps, "tables": len(TABLES),
              "elapsed_seconds": time.perf_counter() - started, "results": results}
    text = json.dumps(output, indent=2) + "\n"
    args.output.write_text(text)
    print(text, end="")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
