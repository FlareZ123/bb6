#!/usr/bin/env python3
"""Generate source-checkable AutoPump certificates for Raw44 B1=0RC, C1=0LE."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
DISCOVER = HERE / "discover.cjs"
AUTOPUMP = ROOT / "im-results/agent48-raw139-f1-oneLA/autopump.py"
OUTPUT = HERE / "0LE-autopump-certs.jsonl"
EXPECTED_SHA256 = "a264eb5744ebc6abc59d2013b3cc962e04cce3de99451fa11e6b8538dfdce611"

proc = subprocess.run(
    ["node", str(DISCOVER), json.dumps({"second": "0LE"})],
    cwd=ROOT, check=True, capture_output=True, text=True,
)
data = json.loads(proc.stdout)
assert data["root"] == "1RB---_1RC0RC_0RD0LE_1LD1LB_------_------"
assert data["rootHoles"] == 5 and data["nodes"] == 33721
assert data["mass"]["open"] == "19125" and len(data["hard"]) == 45
hole_counts = Counter(x["holes"] for x in data["hard"])
assert hole_counts == {1: 40, 2: 4, 3: 1}, hole_counts

spec = importlib.util.spec_from_file_location("bb6_autopump", AUTOPUMP)
autopump = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = autopump
spec.loader.exec_module(autopump)

def parse_table(table):
    slots = [table.split("_")[q][b*3:(b+1)*3] for q in range(6) for b in (0, 1)]
    return [
        24 if x == "---" else 4 * (ord(x[2]) - 65) + 2 * int(x[0]) + (1 if x[1] == "R" else 0)
        for x in slots
    ]

def word(xs):
    return [x if isinstance(x, str) else "*" + x.p for x in xs]

rows = []
pump_costs = []
step_costs = []
entries = []
for i, item in enumerate(data["hard"]):
    result = autopump.find(parse_table(item["table"]), lim=2000)
    if result is None:
        raise RuntimeError(f"AutoPump found no certificate for residual {i}: {item['table']}")
    entry, family, solution = result
    ops, _end = solution
    groups = []
    pending_steps = 0
    pump_cost = 0
    step_cost = 0
    for op in ops:
        if op[0] == "step":
            pending_steps += 1
            step_cost += 1
            continue
        if pending_steps:
            groups.append(pending_steps)
            pending_steps = 0
        side, _q, source_prefix, dest_prefix, pattern, output, k, source_tail, dest_tail = op[3]
        # Action.right stores its left/destination side before its right/source side.
        if side == "L":
            lp, rp, left_tail, right_tail = source_prefix, dest_prefix, source_tail, dest_tail
        else:
            lp, rp, left_tail, right_tail = dest_prefix, source_prefix, dest_tail, source_tail
        groups.append([side, lp, rp, pattern, output, word(left_tail), word(right_tail), k])
        pump_cost += k
    if pending_steps:
        groups.append(pending_steps)
    family_data = [family[0], word(family[1]), word(family[2])]
    rows.append([i, item["table"].replace("_", ""), entry, family_data, pump_cost, step_cost, groups])
    pump_costs.append(pump_cost)
    step_costs.append(step_cost)
    entries.append(entry)

assert len({row[1] for row in rows}) == 45
payload = "".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows)
digest = hashlib.sha256(payload.encode()).hexdigest()
if digest != EXPECTED_SHA256:
    raise RuntimeError(f"AutoPump certificate drift: expected {EXPECTED_SHA256}, got {digest}")
OUTPUT.write_text(payload)
print(json.dumps({
    "child": "B1=0RC,C1=0LE",
    "hard_residuals": len(rows),
    "hole_distribution": dict(sorted(hole_counts.items())),
    "distinct_cost_pairs": len({(r[4], r[5]) for r in rows}),
    "entry_range": [min(entries), max(entries)],
    "pump_cost_range": [min(pump_costs), max(pump_costs)],
    "step_cost_range": [min(step_costs), max(step_costs)],
    "sha256": digest,
    "jsonl_bytes": OUTPUT.stat().st_size,
}, sort_keys=True))
