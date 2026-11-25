#!/usr/bin/env python3
"""Extend the F1=1LD tree and pump search from a prior Actions artifact."""

from collections import Counter
from pathlib import Path
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / "im-results" / "agent48-raw139-f1-oneLA"
sys.path.insert(0, str(GEN))
import scan
import autopump

artifact_root = Path(sys.argv[1])
data_path = next(artifact_root.rglob("f1-14-600.json"))
out = data_path.parent
Path("/tmp/a31-oneLD-outdir.txt").write_text(str(out))
data = json.loads(data_path.read_text())
started = time.monotonic()
initial_unresolved = list(data["unresolved"])

def replace_open(t, target, replacement):
    if t[0] == "open" and t[1] == target:
        return replacement
    if t[0] == "split":
        return [t[0], t[1], t[2], [replace_open(ch, target, replacement) for ch in t[3]]]
    return t

def collect_open(t):
    if t[0] == "open":
        return [t[1]]
    if t[0] == "split":
        out = []
        for ch in t[3]:
            out.extend(collect_open(ch))
        return out
    return []

def recipe_line(index, t, candidate, solution):
    ops, _end = solution
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
    return f"{index} {t} {candidate[0]} {word(candidate[1])} {word(candidate[2])} {','.join(tokens)}"

def find_extended(p, limit=5000, candidate_limit=1200, maxseen=300):
    result = autopump.find(p, limit)
    if result is not None:
        return result
    tr = autopump.trace(p, limit)
    for n, (i, _j, candidate) in enumerate(autopump.candidates(tr)):
        if n >= candidate_limit:
            break
        if len(candidate[1]) + len(candidate[2]) > 16:
            continue
        solution = autopump.solve(p, candidate, autopump.targetnext(candidate), maxseen)
        if solution is not None:
            return i, candidate, solution
    return None

# Refine only the three open leaves left by the first 600-step / width-4 pass.
for old_index in initial_unresolved:
    target = data["open"][old_index]
    local_counts = Counter()
    local_opens = []
    sub = scan.tree(target, local_counts, local_opens, 3000, 4)
    data["tree"] = replace_open(data["tree"], target, sub)
    for key, value in local_counts.items():
        if key == "maxquery":
            data["counts"][key] = max(data["counts"].get(key, 0), value)
        else:
            data["counts"][key] = data["counts"].get(key, 0) - (1 if key == "open" else 0) + value
    existing = {tuple(p) for p in data["open"]}
    for p in local_opens:
        if tuple(p) not in existing:
            existing.add(tuple(p))
            data["open"].append(p)
    print(f"extended old leaf {old_index}: local={dict(local_counts)} newOpen={len(local_opens)}", flush=True)

index = {tuple(p): i for i, p in enumerate(data["open"])}
current_open = collect_open(data["tree"])
unresolved = []
recipes_path = out / "recipes-1LD.txt"
with recipes_path.open("a") as recipes:
    for p in current_open:
        i = index[tuple(p)]
        pump_path = out / f"pump-{i}.json"
        if pump_path.exists():
            continue
        t0 = time.monotonic()
        result = find_extended(p)
        if result is None:
            unresolved.append(i)
            print(f"extended pump {i}: no witness ({time.monotonic()-t0:.1f}s)", flush=True)
            continue
        t, candidate, solution = result
        with pump_path.open("w") as f:
            json.dump({"table": data["parent"], "result": (t, candidate, solution)}, f, default=autopump.js)
        recipes.write(recipe_line(i, t, candidate, solution) + "\n")
        print(f"extended pump {i}: found seed={t}, ops={len(solution[0])} ({time.monotonic()-t0:.1f}s)", flush=True)

data["unresolved"] = sorted(set(unresolved))
data["pump_count"] = len(list(out.glob("pump-*.json")))
data["extended_limit"] = 3000
data["extended_width"] = 4
data_path.write_text(json.dumps(data))
summary = {
    "parent": data["parent"],
    "counts": data["counts"],
    "open_tree_count": len(current_open),
    "pump_count": data["pump_count"],
    "unresolved": data["unresolved"],
    "initial_unresolved": initial_unresolved,
    "elapsed_seconds": round(time.monotonic() - started, 2),
}
(out / "summary-extended.json").write_text(json.dumps(summary, indent=2) + "\n")
print("EXTENSION SUMMARY " + json.dumps(summary), flush=True)
