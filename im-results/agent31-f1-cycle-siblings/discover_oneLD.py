#!/usr/bin/env python3
"""Discover pump witnesses for the raw139 F/1=1LD sibling."""

from collections import Counter
from pathlib import Path
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / "im-results" / "agent48-raw139-f1-oneLA"
OUT = Path(__file__).resolve().parent / "out-oneLD"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(GEN))

import scan
import autopump

PARENT = [7, 24, 11, 24, 14, 21, 3, 16, 12, 11, 24, 14]
LIMIT = 600
MAX_WIDTH = 4
PUMP_LIMIT = 2000

counts = Counter()
opens = []
started = time.monotonic()
tree = scan.tree(PARENT, counts, opens, LIMIT, MAX_WIDTH)
print(f"tree complete: counts={dict(counts)} open={len(opens)} elapsed={time.monotonic()-started:.1f}s", flush=True)

recipes = []
unresolved = []
for i, partial in enumerate(opens):
    t0 = time.monotonic()
    result = autopump.find(partial, PUMP_LIMIT)
    if result is None:
        unresolved.append(i)
        print(f"pump {i}/{len(opens)}: no witness ({time.monotonic()-t0:.1f}s)", flush=True)
        continue
    t, candidate, solution = result
    ops, end = solution
    tokens = []
    steps = 0
    for op in ops:
        if op[0] == "step":
            steps += 1
        else:
            if steps:
                tokens.append(str(steps))
                steps = 0
            pump = op[3]
            side, _q, _sp, dpre, _period, _out, cost, _sr, _dr = pump
            tokens.append(f"{side}{len(dpre)}:{cost}")
    if steps:
        tokens.append(str(steps))

    def word(xs):
        return "".join(x if isinstance(x, str) else f"({x.p})" for x in xs) or "-"

    recipe_line = f"{i} {t} {candidate[0]} {word(candidate[1])} {word(candidate[2])} {','.join(tokens)}"
    recipes.append(recipe_line)
    with (OUT / f"pump-{i}.json").open("w") as f:
        json.dump(
            {"table": PARENT, "result": (t, candidate, solution)},
            f,
            default=autopump.js,
        )
    print(f"pump {i}/{len(opens)}: found seed={t} ops={len(ops)} ({time.monotonic()-t0:.1f}s)", flush=True)

data = {
    "parent": PARENT,
    "counts": dict(counts),
    "open": opens,
    "tree": tree,
    "unresolved": unresolved,
    "pump_count": len(recipes),
    "limit": LIMIT,
    "max_width": MAX_WIDTH,
}
with (OUT / "f1-14-600.json").open("w") as f:
    json.dump(data, f)
(OUT / "recipes-1LD.txt").write_text("\n".join(recipes) + ("\n" if recipes else ""))
summary = {
    "parent": PARENT,
    "counts": dict(counts),
    "open_count": len(opens),
    "pump_count": len(recipes),
    "unresolved": unresolved,
    "elapsed_seconds": round(time.monotonic() - started, 2),
}
(OUT / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print("DISCOVERY SUMMARY " + json.dumps(summary), flush=True)
