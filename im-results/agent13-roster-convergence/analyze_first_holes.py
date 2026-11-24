#!/usr/bin/env python3
"""Reproduce the forced-prefix diagnostic for canonical-124.json."""
import json
from collections import Counter, defaultdict
from pathlib import Path

LETTERS = "ABCDEF"

def simulate(table, cap=10000):
    tape = {}
    seen = {}
    state = 0
    head = 0
    step = 0
    while step < cap:
        relative = tuple(sorted((pos - head, bit) for pos, bit in tape.items() if bit))
        key = (state, relative)
        if key in seen:
            first_step, first_head = seen[key]
            return {
                "kind": "translation-cycle",
                "first": first_step,
                "repeat": step,
                "period": step - first_step,
                "displacement": head - first_head,
            }
        seen[key] = (step, head)
        symbol = tape.get(head, 0)
        slot = state * 2 + symbol
        transition = table[slot]
        if transition is None:
            return {
                "kind": "hole",
                "step": step,
                "slot": LETTERS[state] + str(symbol),
                "state": state,
                "symbol": symbol,
                "head": head,
            }
        write = int(transition[0])
        direction = 1 if transition[1] == "R" else -1
        next_state = LETTERS.index(transition[2])
        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        head += direction
        state = next_state
        step += 1
    return {"kind": "cap", "step": step, "head": head, "state": state, "nonzero": len(tape)}

def main():
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / "canonical-124.json").read_text())
    rows = []
    distribution = Counter()
    by_depth = defaultdict(list)
    for entry in manifest["entries"]:
        result = simulate(entry["table"])
        rows.append({
            "canonical_index": entry["canonical_index"],
            "raw_residual_index": entry["raw_residual_index"],
            "depth": entry["depth"],
            "address": entry["address"],
            "holes": entry["holes"],
            "first_hole": result,
        })
        distribution[result["kind"] + ("@" + str(result["step"]) if result["kind"] == "hole" else "")] += 1
        if result["kind"] == "hole":
            by_depth[entry["depth"]].append(result["step"])
    summary = {
        "schema": "bb6.partial-first-hole-analysis.v1",
        "sample_count": len(rows),
        "distribution": dict(sorted(distribution.items())),
        "by_depth": {
            str(depth): {
                "count": len(steps),
                "steps": sorted(steps),
                "min": min(steps),
                "max": max(steps),
            }
            for depth, steps in sorted(by_depth.items())
        },
        "translation_cycle_count": sum(x["first_hole"]["kind"] == "translation-cycle" for x in rows),
        "cap_count": sum(x["first_hole"]["kind"] == "cap" for x in rows),
        "max_first_hole_steps": max(x["first_hole"]["step"] for x in rows if x["first_hole"]["kind"] == "hole"),
        "entries": rows,
    }
    (here / "first-hole-analysis.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: summary[k] for k in ("sample_count", "distribution", "by_depth", "translation_cycle_count", "max_first_hole_steps")}, indent=2))

if __name__ == "__main__":
    main()
