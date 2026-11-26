#!/usr/bin/env python3
"""Search the eight source-audited Raw124/F1=1LB one-hole leaves for sweep pumps.

This is a discovery tool only.  A candidate is not accepted until its generated
Lean module compiles against SweepPumping and the original project source closure.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
IM = HERE.parent
sys.path.insert(0, str(IM / "agent31-three-hole-tnf"))
sys.path.insert(0, str(IM / "agent10-tnf-multipump"))

import generate_sweeps as sweep  # noqa: E402
import multi  # noqa: E402

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


def windows(events, size: int, count: int):
    if len(events) <= size:
        return [(0, events)]
    last = len(events) - size
    if count <= 1:
        starts = [0]
    else:
        starts = sorted({round(i * last / (count - 1)) for i in range(count)})
    return [(start, events[start : start + size]) for start in starts]


def find_candidate(p, events, max_windows, window_size, max_period, max_entry):
    for start, ev in windows(events, window_size, max_windows):
        if len(ev) < 55:
            continue

        ans = sweep.candidate(p, ev)
        if ans is not None and ans[0] <= max_entry:
            return "single-block", ans, start, sweep.generate

        ans = multi.candidate(p, ev)
        if ans is not None and ans[0] <= max_entry:
            return "multi-block", ans, start, multi.generate

        for side in ("L", "R"):
            for q in range(6):
                for period in range(1, max_period + 1):
                    ans = multi.long_candidate(
                        p, ev, side, q, period, maxdiff=64
                    )
                    if ans is not None and ans[0] <= max_entry:
                        return f"long-{side}-q{q}-p{period}", ans, start, multi.generate
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=100_000)
    ap.add_argument("--max-windows", type=int, default=32)
    ap.add_argument("--window-size", type=int, default=160)
    ap.add_argument("--max-period", type=int, default=8)
    ap.add_argument("--max-entry", type=int, default=250_000)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)

    modules = [
        "import SweepPumping",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "set_option linter.unusedVariables false",
        "namespace BB6Coverage.Agent31Pump",
        "open BB6Coverage",
    ]
    summary = []

    for rid, source in TABLES:
        p = sweep.parse(source)
        events = sweep.concrete_events(p, limit=args.limit)
        found = find_candidate(
            p, events, args.max_windows, args.window_size,
            args.max_period, args.max_entry
        )
        item = {
            "id": rid,
            "table": source,
            "limit": args.limit,
            "event_count": len(events),
            "last_event_step": events[-1][0] if events else None,
            "candidate": None,
        }
        if found is not None:
            kind, ans, window_start, generator = found
            code, info = generator(f"Raw124R{rid}", p, ans)
            modules.append(code)
            item["candidate"] = {
                "kind": kind,
                "window_start": window_start,
                "entry_step": info[0],
                "fixed_steps": info[1],
                "pump_steps": info[2],
            }
            print(f"FOUND {rid}: {item['candidate']}", flush=True)
        else:
            print(
                f"NO-CANDIDATE {rid}: events={len(events)} "
                f"last_event_step={item['last_event_step']}",
                flush=True,
            )
        summary.append(item)

    if len(modules) > 6:
        modules.append("end BB6Coverage.Agent31Pump")
        (args.out / "Raw1241LBResidualPumps.lean").write_text(
            "\n\n".join(modules) + "\n", encoding="utf-8"
        )
    (args.out / "search.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Generated {len(modules)-6} candidate module(s)", flush=True)


if __name__ == "__main__":
    main()
