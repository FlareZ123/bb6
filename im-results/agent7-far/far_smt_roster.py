#!/usr/bin/env python3
"""Sharded QF_BV search over a finite roster of one-hole partial machines.

This is an untrusted candidate generator. Every emitted HIT is independently
checked by Lean's Data.fastValid_sound in agent7-far-hard-root.yml.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

from z3 import sat, unsat

from far_smt_compose import parse_table, solve_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("roster", type=Path)
    parser.add_argument("--shard", type=int, required=True)
    parser.add_argument("--shards", type=int, required=True)
    parser.add_argument("--min-dfa", type=int, default=1)
    parser.add_argument("--max-dfa", type=int, default=6)
    parser.add_argument("--timeout-ms", type=int, default=2000)
    args = parser.parse_args()

    if args.shards < 1 or not 0 <= args.shard < args.shards:
        parser.error("require 0 <= --shard < --shards")
    if not 1 <= args.min_dfa <= args.max_dfa <= 10:
        parser.error("require 1 <= --min-dfa <= --max-dfa <= 10")
    if args.timeout_ms <= 0:
        parser.error("--timeout-ms must be positive")

    lines = [line.strip() for line in args.roster.read_text().splitlines() if line.strip()]
    if not lines:
        parser.error("roster is empty")

    searched = 0
    hits = 0
    for line_number, code in enumerate(lines, 1):
        if (line_number - 1) % args.shards != args.shard:
            continue
        searched += 1
        table = parse_table(code)
        print(
            f"SMT target line={line_number} shard={args.shard}/{args.shards} code={code}",
            file=sys.stderr,
            flush=True,
        )
        found = False
        for d in range(args.min_dfa, args.max_dfa + 1):
            for reflected in (False, True):
                print(
                    f"trying line={line_number} dfa={d} reflected={int(reflected)} "
                    f"timeout_ms={args.timeout_ms}",
                    file=sys.stderr,
                    flush=True,
                )
                result, cert, reason = solve_one(table, d, reflected, args.timeout_ms)
                if result == sat:
                    dfa, masks0, masks1, zmask = cert
                    print(
                        "HIT", line_number, code, d, int(reflected), "DFA", *dfa,
                        "MASK", *masks0, *masks1, "Z", zmask,
                        flush=True,
                    )
                    hits += 1
                    found = True
                    break
                if result == unsat:
                    print(
                        f"UNSAT line={line_number} dfa={d} reflected={int(reflected)}",
                        file=sys.stderr,
                        flush=True,
                    )
                else:
                    print(
                        f"UNKNOWN line={line_number} dfa={d} reflected={int(reflected)} "
                        f"reason={reason}",
                        file=sys.stderr,
                        flush=True,
                    )
            if found:
                break
        if not found:
            print(
                f"NO_SMT_CERTIFICATE line={line_number} code={code}",
                file=sys.stderr,
                flush=True,
            )

    print(
        f"ROSTER_SHARD_COMPLETE shard={args.shard}/{args.shards} "
        f"searched={searched} hits={hits}",
        file=sys.stderr,
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
