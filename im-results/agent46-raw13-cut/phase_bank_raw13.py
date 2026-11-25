#!/usr/bin/env python3
"""Apply reusable two-sided DFA certificates to every raw13 residual.

The bank combines independently discovered pairs from Agent25's raw123 work,
Agent3's raw120 work, and Agent1's raw118/raw120 SAT work.  Imported pairs are
only candidate data: for each exact raw13 partial table, bidfa_emit.witness
reconstructs the reachable abstract closure and rejects any pair that can
read an unassigned/halting slot.  The generated Lean audit remains the
acceptance gate.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
IM = ROOT.parent
sys.path.insert(0, str(IM / "agent16-raw118"))
from bidfa_emit import witness

# HardRootLeaves.D3 (the 24-step hard root; distinct from other D-family labels).
D3_TABLE = "1RB0LC1RC1RE1LA0LD0RB0RA1RB1RF1RD---"


def compatible_partial(partial: str, full: str) -> bool:
    return all(
        partial[i:i + 3] == "---" or partial[i:i + 3] == full[i:i + 3]
        for i in range(0, 36, 3)
    )


def add_pair(bank, name, dl, dr, table=None, claimed=None):
    """Validate a source table when available, then deduplicate a DFA pair."""
    if table is not None:
        try:
            edges, states = witness(table, dl, dr)
        except (ValueError, IndexError):
            return
        actual = (len(states), sum(len(side) for side in edges))
        if claimed is not None and actual != tuple(claimed):
            print(f"{name}: recomputed size {actual} differs from stored metadata {claimed}; using recomputed size")
    else:
        if claimed is None:
            raise SystemExit(f"{name}: no source table or claimed size")
        actual = tuple(claimed)
    key = json.dumps([dl, dr], separators=(",", ":"))
    if key not in bank:
        bank[key] = {"dl": dl, "dr": dr, "states": actual[0],
                     "edges": actual[1], "sources": [name]}
    else:
        bank[key]["sources"].append(name)
        if actual < (bank[key]["states"], bank[key]["edges"]):
            bank[key]["states"], bank[key]["edges"] = actual


def load_bank():
    bank = {}

    # Five already-minimized phase-aware pairs.
    phase = json.loads((IM / "agent25-raw123" / "spec.json").read_text())["bidfa"]
    for ident in ("8156", "8175", "8155", "8174", "573"):
        dl, dr, states, edges = phase[ident]
        add_pair(bank, f"agent25-raw123:{ident}", dl, dr, claimed=(states, edges))

    # Agent3's source-linked raw120 BiDFA candidates, validated against their
    # original partial tables before being admitted to the reusable bank.
    for ident, value in json.loads((IM / "agent3-tnf-raw120" / "1LB-bidfa.json").read_text()).items():
        table, dl, dr = value
        add_pair(bank, f"agent3-raw120-1LB:{ident}", dl, dr, table=table)
    for ident, value in json.loads((IM / "agent3-tnf-raw120" / "ra-bidfa.json").read_text()).items():
        table, dl, dr, states, edges = value
        add_pair(bank, f"agent3-raw120-RA:{ident}", dl, dr,
                 table=table, claimed=(states, edges))

    # Agent1's SAT-discovered raw118/raw120 pairs.  Recheck the source tables
    # with the same sparse-closure checker; SAT discovery itself is not trusted.
    for filename, source in (
        ("raw118-sat-hits.json", "agent1-raw118-SAT"),
        ("raw120-1lb-hits.json", "agent1-raw120-SAT"),
    ):
        entries = json.loads((IM / "agent1-bidfa-sat" / filename).read_text())
        for entry in entries:
            add_pair(bank, f"{source}:{entry['index']}",
                     entry["left"], entry["right"], table=entry["table"],
                     claimed=(entry["states"], entry["edges"]))

    return sorted(bank.values(),
                  key=lambda x: (x["states"], x["edges"], x["sources"][0]))


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
    holes = Counter(table.count("---") for table in rows.values())
    d3_ids = [ident for ident, table in rows.items()
              if compatible_partial(table, D3_TABLE)]
    if len(d3_ids) > 1:
        raise SystemExit(f"D3 appears in overlapping raw13 residuals: {d3_ids}")
    d3_id = d3_ids[0] if d3_ids else None

    bank = load_bank()
    if not bank:
        raise SystemExit("no reusable BiDFA bank pairs were loaded")

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

    source_hits = defaultdict(int)
    best_sources: dict[str, str] = {}
    newly_closed: dict[str, str] = {}
    improvements = 0
    for ident in sorted(rows):
        table = rows[ident]
        best = None
        best_source = None
        for pair in bank:
            try:
                edges, states = witness(table, pair["dl"], pair["dr"])
            except ValueError:
                continue
            source_hits[pair["sources"][0]] += 1
            candidate = [pair["dl"], pair["dr"], len(states),
                         sum(len(side) for side in edges)]
            if best is None or (candidate[2], candidate[3]) < (best[2], best[3]):
                best = candidate
                best_source = pair["sources"][0]
        if best is None:
            continue
        key = str(ident)
        old = bidfa.get(key)
        if old is None or (best[2], best[3]) < (old[2], old[3]):
            bidfa[key] = best
            improvements += 1
        newly_closed[key] = best_source
        best_sources[key] = best_source

    searches.append({
        "method": "multi-source-bidfa-bank",
        "bank_pair_count": len(bank),
        "bank_sources": sorted({s for pair in bank for s in pair["sources"]}),
        "tested_count": len(rows),
        "hole_counts": {str(k): holes[k] for k in sorted(holes)},
        "source_hits": dict(sorted(source_hits.items())),
        "new_candidate_ids": sorted(newly_closed, key=int),
        "best_sources": best_sources,
        "improved_or_added": improvements,
        "d3_raw13_residual_id": d3_id,
        "d3_closed_by_bank": d3_id is not None and str(d3_id) in newly_closed,
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
    print(f"tested={len(rows)} bank_pairs={len(bank)}")
    print(f"source_hits={json.dumps(dict(sorted(source_hits.items())), sort_keys=True)}")
    print(f"newly_closed={len(newly_closed)} improved_or_added={improvements}")
    print(f"total_candidates={len(bidfa)}")
    print(f"d3_raw13_residual_id={d3_id}")
    print(f"d3_closed_by_bank={d3_id is not None and str(d3_id) in newly_closed}")
    print("candidate_ids=" + ",".join(sorted(bidfa, key=int)))
    print("source_open_sha256=" + open_sha)


if __name__ == "__main__":
    main()
