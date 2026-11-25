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
    args = ap.parse_args()

    residual_file = ROOT / "raw13-open-residuals.txt"
    raw_bytes = residual_file.read_bytes()
    rows: dict[int, str] = {}
    for line in raw_bytes.decode().splitlines():
        ident, table = line.split()
        rows[int(ident)] = table
    if len(rows) != 1716:
        raise SystemExit(f"expected 1716 raw13 open residuals, found {len(rows)}")

    ids = sorted(rows)
    if args.limit <= 0 or args.limit >= len(ids):
        sample = ids
    else:
        sample = sorted(random.Random(args.seed).sample(ids, args.limit))

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

    bidfa: dict[str, list[object]] = {}
    for line in result.stdout.splitlines():
        parts = line.split()
        if len(parts) != 14:
            raise SystemExit(f"unexpected phase.cpp result line: {line[:300]}")
        ident = int(parts[0])
        if ident not in rows or ident not in sample:
            raise SystemExit(f"phase.cpp returned unrequested residual {ident}")
        left = parse_dfa(parts[12])
        right = parse_dfa(parts[13])
        minimized = minimize(rows[ident], left, right)
        dl, dr, states, edges = minimized
        bidfa[str(ident)] = [dl, dr, states, edges]

    spec = {
        "parent": "1RB1LC1RC0LD1LA0RB1LB1LE1RF0LA---0RE",
        "open_sha256": hashlib.sha256(raw_bytes).hexdigest(),
        "source_count": len(rows),
        "sample_seed": args.seed,
        "sample_limit": len(sample),
        "sample_ids": sample,
        "state_cap": args.cap,
        "bidfa": bidfa,
    }
    out = ROOT / "raw13-bidfa-spec.json"
    out.write_text(json.dumps(spec, separators=(",", ":")) + "\n")
    print(f"searched={len(sample)} candidates={len(bidfa)}")
    print(f"open_sha256={spec['open_sha256']}")
    print(f"candidate_ids={','.join(sorted(bidfa, key=int))}")


if __name__ == "__main__":
    main()
