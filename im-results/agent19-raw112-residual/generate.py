#!/usr/bin/env python3
"""Search late blank-tape boundary events for a one-block inductive pump.

This is discovery only: every generated equation is checked by Lean through
SweepPumping, and the resulting NeverHalts theorem is source-audited in CI.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
import generate_sweeps as gs

TABLE = "1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE"
OUT = ROOT / "Raw112Residual0LE.lean"


def main():
    p = gs.parse(TABLE)
    ev = gs.concrete_events(p, limit=100_000)
    print(f"table={gs.show(p)} events={len(ev)}")
    # The first 60 boundary events miss this leaf's stable pump. Search
    # overlapping 60-event windows, prioritizing the late-growth region.
    starts = list(range(60, max(61, len(ev) - 59)))
    starts.sort(key=lambda x: (abs(x - 90), x))
    for start in starts:
        window = ev[start:start + 60]
        if len(window) < 20:
            continue
        ans = gs.candidate(p, window)
        if ans is None:
            continue
        code, info = gs.generate(0, p, ans)
        t, intercept, slope = info
        text = "\n\n".join([
            "import SweepPumping",
            "set_option maxRecDepth 100000",
            "set_option maxHeartbeats 0",
            "set_option linter.unusedVariables false",
            "namespace BB6Coverage.Agent19Raw112Residual0LE",
            "open BB6Coverage",
            "open BB6Coverage.Agent31Pump",
            code,
            "end BB6Coverage.Agent19Raw112Residual0LE",
            "",
        ])
        OUT.write_text(text, encoding="utf-8")
        print(f"FOUND window={start} entry={t} intercept={intercept} slope={slope}")
        print(f"generated={OUT} bytes={OUT.stat().st_size}")
        return
    OUT.unlink(missing_ok=True)
    print("NO_CANDIDATE")


if __name__ == "__main__":
    main()
