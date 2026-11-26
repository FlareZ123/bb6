#!/usr/bin/env python3
"""Longer-cap side-cycle/last-hole probe for the eight Raw124 F1=1LB leaves.

The C++ classifier's hashes only select candidates; its tape comparison checks
translated side-cycle equality directly.  Output remains discovery data until
the resulting leaves are assembled and checked by the Lean PartialAudit.
"""
from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent

TABLES = [
    ("207", "1RB0LA1RC0LB0RD0RF1LD1RE---1LF1RA1LB"),
    ("209", "1RB0LF1RC0LB0RD0RF1LD1RE---1LF1RA1LB"),
    ("212", "1RB1LA1RC0LB0RD0RF1LD1RE---1LF1RA1LB"),
    ("217", "1RB1RA1RC0LB0RD0RF1LD1RE---1LF1RA1LB"),
    ("711", "1RB1LA1RC0LF0RD0RA1LD1RE---1LF1LA1LB"),
    ("937", "1RB---1RC0LF0RD0RA1LD1RE1RD1LF1RE1LB"),
    ("980", "1RB0LE1RC0RA0RD---1LD1RE1LA1LF1LE1LB"),
    ("2083", "1RB0LA1RC1LE0RD0RA1LD1RE1LC1LF---1LB"),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cap", type=int, default=1_000_000)
    ap.add_argument("--lookback", type=int, default=128)
    ap.add_argument("--sim-cap", type=int, default=1_000_000_000)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)

    exe = args.out / "fast_partition"
    subprocess.run(
        ["g++", "-std=c++20", "-O3", str(HERE / "fast_partition.cpp"), "-o", str(exe)],
        check=True,
    )

    summary = []
    for rid, table in TABLES:
        prefix = args.out / f"residual-{rid}"
        proc = subprocess.run(
            [str(exe), table, str(args.cap), str(args.lookback), str(prefix)],
            check=True, capture_output=True, text=True,
        )
        tree = json.loads(prefix.with_suffix(".json").read_text(encoding="utf-8"))
        open_rows = prefix.with_suffix(".open").read_text(encoding="utf-8").splitlines()
        item = {
            "id": rid,
            "table": table,
            "cap": args.cap,
            "lookback": args.lookback,
            "stdout": proc.stdout.strip(),
            "tree": tree,
            "open_rows": open_rows,
        }
        summary.append(item)
        print(f"{rid}: {proc.stdout.strip()} tree={tree}", flush=True)

    (args.out / "partition-probe.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )

    sim_exe = args.out / "simulate_1lb_residuals"
    subprocess.run(
        ["g++", "-std=c++20", "-O3", str(HERE / "simulate_1lb_residuals.cpp"), "-o", str(sim_exe)],
        check=True,
    )
    sim_input = "\n".join(f"{rid} {table}" for rid, table in TABLES) + "\n"
    sim_proc = subprocess.run(
        [str(sim_exe), str(args.sim_cap)], input=sim_input,
        check=True, capture_output=True, text=True,
    )
    simulation = [json.loads(line) for line in sim_proc.stdout.splitlines() if line.strip()]
    for item in simulation:
        print(f"LONG-RUN {item}", flush=True)
    (args.out / "long-run-simulation.json").write_text(
        json.dumps(simulation, indent=2) + "\n", encoding="utf-8"
    )



if __name__ == "__main__":
    main()
