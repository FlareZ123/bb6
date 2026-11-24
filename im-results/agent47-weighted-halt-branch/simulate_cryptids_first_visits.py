#!/usr/bin/env python3
"""Deterministically simulate first visits to the 12 state/symbol rows.

Usage:
  python simulate_cryptids_first_visits.py path/to/Cryptids608NonHalt.lean

This is an exploratory trace tool, not a proof of nonhalting or a Lean
refinement-path certificate. The nonhalting proofs remain the source of truth.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path


ROW = re.compile(
    r"\|\s*(\d+),\s*(false|true)\s*=>\s*"
    r"(none|some\s*⟨(true|false),\s*(true|false),\s*(\d+)⟩)"
)


def parse_machine(source: str, index: int):
    start = source.index(f"def expectedRLE_r{index} : Machine")
    end = source.index(f"theorem original_r{index}_eq_expectedRLE", start)
    block = source[start:end]
    rows = [[None, None] for _ in range(6)]
    for match in ROW.finditer(block):
        state = int(match.group(1))
        symbol = int(match.group(2) == "true")
        if match.group(3) == "none":
            rows[state][symbol] = None
        else:
            rows[state][symbol] = {
                "write": int(match.group(4) == "true"),
                "right": match.group(5) == "true",
                "next": int(match.group(6)),
            }
    return rows


def simulate(rows):
    tape: dict[int, int] = {}
    state = 0
    head = 0
    first_visit: dict[str, int] = {}
    steps = 0
    ordinary = sum(move is not None for row in rows for move in row)
    while steps < 1_000_000 and len(first_visit) < ordinary:
        symbol = tape.get(head, 0)
        slot = f"{state}/{symbol}"
        first_visit.setdefault(slot, steps)
        move = rows[state][symbol]
        if move is None:
            return {
                "halts_at": steps,
                "first_visits": first_visit,
                "ordinary_rows": ordinary,
                "all_ordinary_seen": len(first_visit) == ordinary,
            }
        tape[head] = move["write"]
        head += 1 if move["right"] else -1
        state = move["next"]
        steps += 1
    return {
        "halts_at": None,
        "steps_at_coverage": steps,
        "first_visits": first_visit,
        "ordinary_rows": ordinary,
        "all_ordinary_seen": len(first_visit) == ordinary,
        "unvisited_ordinary": [
            f"{s}/{b}"
            for s, row in enumerate(rows)
            for b, move in enumerate(row)
            if move is not None and f"{s}/{b}" not in first_visit
        ],
        "halt_slots": [
            f"{s}/{b}"
            for s, row in enumerate(rows)
            for b, move in enumerate(row)
            if move is None
        ],
    }


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    source = Path(sys.argv[1]).read_text(encoding="utf-8")
    results = {}
    for index in range(1, 7):
        rows = parse_machine(source, index)
        results[f"r{index}"] = simulate(rows)
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
