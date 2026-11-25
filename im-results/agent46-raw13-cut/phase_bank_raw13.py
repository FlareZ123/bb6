#!/usr/bin/env python3
"""Apply Agent25's five source-audited phase-BiDFA pairs to every raw13 residual.

The imported bank is only a set of candidate automata.  bidfa_emit.witness
reconstructs the reachable abstract closure for each exact partial table and
raises if any completion can reach an unassigned/halting slot.  The existing
Lean audit remains the acceptance gate.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
IM = ROOT.parent
sys.path.insert(0, str(IM / "agent16-raw118"))
from bidfa_emit import witness

BANK_PATH = IM / "agent25-raw123" / "spec.json"
BANK_IDS = ("8156", "8175", "8155", "8174", "573")
# Literal D3 rooted machine, with its unique undefined F1 transition.
D3_TABLE = "1RB0LC1RC1RE1LA0LD0RB0RA1RB1RF1RD---"


def compatible_partial(partial: str, full: str) -> bool:
    return all(
        partial[i:i + 3] == "---" or partial[i:i + 3] == full[i:i + 3]
        for i in range(0, 36, 3)
    )


def main() -> None:
    residual_path = ROOT / "raw13-open-residuals.txt"
    raw_bytes = residual_path.read_bytes()
    rows: dict[int, str] = {}
    for line in raw_bytes.decode().splitlines():
        ident, table = line.split()
        rows[int(ident)] = table
    if not rows:
        raise SystemExit("raw13 residual file is empty")

    open_sha = hashlib.sha256(raw_bytes).hexdigest()
    source = json.loads(BANK_PATH.read_text())
    bank = source.get("bidfa", {})
    missing = [key for key in BANK_IDS if key not in bank]
    if missing:
        raise SystemExit(f"missing phase bank entries: {missing}")

    holes = Counter(table.count("---") for table in rows.values())
    d3_ids = [ident for ident, table in rows.items()
              if compatible_partial(table, D3_TABLE)]
    if len(d3_ids) > 1:
        raise SystemExit(f"D3 appears in overlapping raw13 residuals: {d3_ids}")
    d3_id = d3_ids[0] if d3_ids else None
    out_path = ROOT / "raw13-bidfa-spec.json"
    if out_path.exists():
        spec = json.loads(out_path.read_text())
        if spec.get("source_count") != len(rows) or spec.get("open_sha256") != open_sha:
            raise SystemExit("existing raw13 BiDFA spec belongs to another residual source")
        bidfa = dict(spec.get("bidfa", {}))
        searches = list(spec.get("searches", []))
    else:
        bidfa = {}
        searches = []

    newly_closed: dict[str, str] = {}
    improvements = 0
    for ident in sorted(rows):
        table = rows[ident]
        best = None
        best_source = None
        for bank_id in BANK_IDS:
            dl, dr, _, _ = bank[bank_id]
            try:
                edges, states = witness(table, dl, dr)
            except ValueError:
                continue
            candidate = [dl, dr, len(states), sum(len(side) for side in edges)]
            if best is None or (candidate[2], candidate[3]) < (best[2], best[3]):
                best = candidate
                best_source = bank_id
        if best is None:
            continue
        key = str(ident)
        old = bidfa.get(key)
        if old is None or (best[2], best[3]) < (old[2], old[3]):
            bidfa[key] = best
            improvements += 1
        newly_closed[key] = best_source

    searches.append({
        "method": "agent25-raw123-phase-bank",
        "bank_ids": list(BANK_IDS),
        "tested_count": len(rows),
        "hole_counts": {str(k): holes[k] for k in sorted(holes)},
        "new_candidate_ids": sorted(newly_closed, key=int),
        "improved_or_added": improvements,
        "d3_raw13_residual_id": d3_id,
        "d3_closed_by_phase_bank": d3_id is not None and str(d3_id) in bidfa,
    })
    result = {
        "parent": "1RB---1RC---1LA---------------------",
        "open_sha256": open_sha,
        "source_count": len(rows),
        "hole_counts": {str(k): holes[k] for k in sorted(holes)},
        "searches": searches,
        "bidfa": bidfa,
    }
    out_path.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(f"tested={len(rows)} bank_pairs={len(BANK_IDS)}")
    print(f"newly_closed={len(newly_closed)} improved_or_added={improvements}")
    print(f"total_candidates={len(bidfa)}")
    print(f"d3_raw13_residual_id={d3_id}")
    print(f"d3_closed_by_phase_bank={d3_id is not None and str(d3_id) in bidfa}")
    print("candidate_ids=" + ",".join(sorted(bidfa, key=int)))
    print("source_open_sha256=" + open_sha)


if __name__ == "__main__":
    main()
