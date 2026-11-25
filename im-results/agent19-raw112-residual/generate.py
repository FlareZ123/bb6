#!/usr/bin/env python3
"""Discover a multi-block affine sweep for the raw112 F1=0LE residual.

The event bound and search windows deliberately extend past the first 60
boundary events; this leaf's stable tape structure appears much later.
Generated Lean is checked by SweepPumping and the import-closure audit.
"""
from pathlib import Path
import sys
from collections import defaultdict

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
sys.path.insert(0, str(ROOT.parent / "agent47-raw114-cut"))
import generate_sweeps as pump
import multi_sweep as ms

TABLE = "1RB0RF_1RC0LB_0RD0LB_1LD1RE_0RA1LC_---0LE"
OUT = ROOT / "Raw112Residual0LE.lean"


def discover_extended(p, limit=100_000, maxrep=5, maxlen=32, maxgap=16,
                      max_events=240, execute_limit=1_000):
    ev = pump.concrete_events(p, limit)
    groups = defaultdict(list)
    for t, side, c in ev:
        if (side == "L" and c.l.pre == "") or (side == "R" and c.r.pre == ""):
            groups[side, c.q].append((t, c.r.pre if side == "L" else c.l.pre))
    sizes = sorted(((len(g), side, q) for (side, q), g in groups.items()), reverse=True)
    print(f"boundary_events={len(ev)} groups={sizes}")
    attempted = set()
    # Search the full event history, not just the early prefix used by the
    # original generator.  This catches later counter phases.
    for (side, q), g in sorted(groups.items(), key=lambda item: -len(item[1])):
        upto = min(len(g), max_events)
        for i, (t, a) in enumerate(g[:upto]):
            if i % 25 == 0:
                print(f"search side={side} q={q} i={i}/{upto}")
            for j in range(i + 1, min(i + maxgap + 1, len(g))):
                _, b = g[j]
                diff = len(b) - len(a)
                if not 1 <= diff <= maxlen:
                    continue
                for k in range(j + 1, min(j + maxgap + 1, len(g))):
                    _, c = g[k]
                    if len(c) - len(b) != diff:
                        continue
                    for w in ms.infer(a, b, c, maxrep=maxrep, maxlen=maxlen):
                        if sum(isinstance(x, ms.Rep) for x in w.parts) < 2:
                            continue
                        v = w.inc()
                        start = ms.Config(q, ms.Word(), w) if side == "L" else ms.Config(q, w, ms.Word())
                        target = ms.Config(q, ms.Word(), v) if side == "L" else ms.Config(q, v, ms.Word())
                        if (start, target) in attempted:
                            continue
                        attempted.add((start, target))
                        res = ms.execute(p, start, target, limit=execute_limit)
                        if res:
                            print(f"FOUND side={side} q={q} entry={t} "
                                  f"parts={w.parts} attempts={len(attempted)}")
                            return t, start, target, res
    print(f"NO_MULTI_BLOCK_PUMP attempts={len(attempted)}")
    return None


def main():
    p = pump.parse(TABLE)
    ans = discover_extended(p)
    if ans is None:
        OUT.unlink(missing_ok=True)
        return
    code, info = ms.generate(0, p, ans)
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
    print(f"GENERATED entry={t} intercept={intercept} slope={slope}")
    print(f"generated={OUT} bytes={OUT.stat().st_size}")


if __name__ == "__main__":
    main()
