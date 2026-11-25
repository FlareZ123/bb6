#!/usr/bin/env python3
"""Search a reproducible sample of raw13 open residuals for phase-aware BiDFA invariants.

The C++ search is untrusted candidate discovery. Every returned automaton is
replayed by Agent16's independent Python witness/minimizer and then emitted
as a Lean proof checked against the repository's original machine semantics.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import subprocess
import tempfile
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
IM = ROOT.parent
D3_TABLE = "1RB0LC1RC1RE1LA0LD0RB0RA1RB1RF1RD---"


def compatible_partial(partial: str, full: str) -> bool:
    return all(
        partial[i:i + 3] == "---" or partial[i:i + 3] == full[i:i + 3]
        for i in range(0, 36, 3)
    )
sys.path.insert(0, str(IM / "agent25-raw123"))
from minimize_phase import minimize


def parse_dfa(token: str) -> list[int]:
    count, payload = token.split(":", 1)
    values = [int(x) for x in payload.split(",") if x]
    if len(values) != 2 * int(count):
        raise ValueError(f"bad DFA transition vector: {token[:120]}")
    return values


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=25,
                    help="number of residuals to sample; 0 means all")
    ap.add_argument("--cap", type=int, default=5000,
                    help="abstract-state cap for each candidate search")
    ap.add_argument("--seed", type=int, default=46)
    ap.add_argument("--exclude-d3", action="store_true",
                    help="exclude the known halting D3 hard-root descendant from nonhalting search")
    args = ap.parse_args()

    residual_file = ROOT / "raw13-open-residuals.txt"
    raw_bytes = residual_file.read_bytes()
    rows: dict[int, str] = {}
    for line in raw_bytes.decode().splitlines():
        ident, table = line.split()
        rows[int(ident)] = table
    if not rows:
        raise SystemExit("raw13 open residual file is empty; regenerate the cut first")

    ids = sorted(rows)
    d3_ids = [ident for ident, table in rows.items()
              if compatible_partial(table, D3_TABLE)]
    if len(d3_ids) > 1:
        raise SystemExit(f"D3 appears in overlapping raw13 residuals: {d3_ids}")
    excluded_ids = d3_ids if args.exclude_d3 else []
    groups: dict[int, list[int]] = {}
    for ident, table in rows.items():
        if ident not in excluded_ids:
            groups.setdefault(table.count("---"), []).append(ident)
    hole_counts = {str(k): len(v) for k, v in sorted(groups.items())}
    if args.limit <= 0 or args.limit >= len(ids):
        sample = [ident for ident in ids if ident not in excluded_ids]
    else:
        rng = random.Random(args.seed)
        for values in groups.values():
            rng.shuffle(values)
        sample = []
        while len(sample) < args.limit and any(groups.values()):
            for holes in sorted(groups):
                if groups[holes] and len(sample) < args.limit:
                    sample.append(groups[holes].pop())
        sample.sort()
    sample_hole_counts = {}
    for ident in sample:
        key = str(rows[ident].count("---"))
        sample_hole_counts[key] = sample_hole_counts.get(key, 0) + 1

    cpp = IM / "agent25-raw123" / "phase.cpp"
    with tempfile.TemporaryDirectory(prefix="raw13-phase-") as tmp:
        tmpdir = Path(tmp)
        exe = tmpdir / "phase"
        subprocess.run(
            ["g++", "-std=c++17", "-O3", str(cpp), "-o", str(exe)],
            check=True,
        )
        payload = "".join(f"{i} {rows[i]}\n" for i in sample)
        result = subprocess.run(
            [str(exe), str(args.cap)],
            input=payload,
            text=True,
            capture_output=True,
            check=True,
        )

    (ROOT / "raw13-phase-search.stdout.txt").write_text(result.stdout)
    (ROOT / "raw13-phase-search.stderr.txt").write_text(result.stderr)

    open_sha = hashlib.sha256(raw_bytes).hexdigest()
    out = ROOT / "raw13-bidfa-spec.json"
    bidfa: dict[str, list[object]] = {}
    searches = []
    if out.exists():
        prior = json.loads(out.read_text())
        if prior.get("source_count") != len(rows) or prior.get("open_sha256") != open_sha:
            raise SystemExit("existing raw13 BiDFA spec belongs to a different residual source")
        bidfa.update(prior.get("bidfa", {}))
        searches.extend(prior.get("searches", []))

    new_candidates = {}
    for line in result.stdout.splitlines():
        parts = line.split()
        if len(parts) != 14:
            raise SystemExit(f"unexpected phase.cpp result line: {line[:300]}")
        ident = int(parts[0])
        if ident not in rows or ident not in sample:
            raise SystemExit(f"phase.cpp returned unrequested residual {ident}")
        left = parse_dfa(parts[12])
        right = parse_dfa(parts[13])
        dl, dr, states, edges = minimize(rows[ident], left, right)
        candidate = [dl, dr, states, edges]
        key = str(ident)
        old = bidfa.get(key)
        if old is None or (states, edges) < (old[2], old[3]):
            bidfa[key] = candidate
        new_candidates[key] = candidate

    searches.append({
        "seed": args.seed,
        "sample_ids": sample,
        "excluded_ids": excluded_ids,
        "sample_hole_counts": sample_hole_counts,
        "state_cap": args.cap,
        "new_candidate_ids": sorted(new_candidates, key=int),
    })
    spec = {
        "parent": "1RB---1RC---1LA---------------------",
        "open_sha256": open_sha,
        "source_count": len(rows),
        "hole_counts": hole_counts,
        "searches": searches,
        "bidfa": bidfa,
    }
    out.write_text(json.dumps(spec, separators=(",", ":")) + "\n")
    print(f"searched={len(sample)} new_candidates={len(new_candidates)} total_candidates={len(bidfa)}")
    print(f"open_sha256={spec['open_sha256']}")
    print(f"candidate_ids={','.join(sorted(bidfa, key=int))}")



if __name__ == "__main__":
    main()
