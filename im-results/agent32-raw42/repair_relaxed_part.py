#!/usr/bin/env python3
"""Repair only private dependencies of an exact frozen partition.

All leaf candidates (including small list certificates) are converted to
the unchanged FastBiDFA checker, with a bounded relaxed quotient search.
Original root membership, cut trees, tables and theorem types are retained.
"""
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from repair_exact_part import dependencies
from relaxed_quotient import transform as compact
from prefix_rewrite import transform as prefix


def repair(g, branch, part):
    plan = json.loads((g / "split-plan.json").read_text())
    assert plan["artifact_prefix"] == "raw42-split-" + branch
    groups = plan["groups"]
    assert part in groups
    usage = defaultdict(set)
    for key, roots in groups.items():
        for m in dependencies(g, roots):
            usage[m].add(key)
    count = checks = shared = 0
    totals = [0, 0, 0]
    for m in sorted(usage):
        if part not in usage[m] or usage[m] != {part}:
            continue
        f = g / (m + ".lean")
        src = f.read_text()
        if re.fullmatch(r"Raw42" + branch + r"(NGram|Run)\d+", m):
            out, b, base, a, n = compact(src)
            f.write_text(out)
            print(m, b, "->", base, "->", a, "attempts", n, flush=True)
            totals = [x + y for x, y in zip(totals, (b[-1], base[-1], a[-1]))]
            count += 1
        elif m.startswith("Raw42" + branch + "ClosedRoot"):
            out, n, s, _ = prefix(src, branch)
            if n:
                f.write_text(out)
                checks += n
                shared += s
    print("partition", branch, part, "leaves", count, "joint states", totals,
          "root checks", checks, "prefix-shared checks", shared, flush=True)


if __name__ == "__main__":
    repair(Path(sys.argv[1]), sys.argv[2], sys.argv[3])
