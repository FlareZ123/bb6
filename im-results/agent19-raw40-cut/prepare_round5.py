#!/usr/bin/env python3
"""Regenerate the complete 0LA_0LB five-hole weighted bound proof."""
import json, os, pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
out = root / "round5" / "0LA_0LB"
out.mkdir(parents=True, exist_ok=True)
p = "1RB0LA_1RC---_0RD0LB_1LD1LA_------_------"
def run(args, **kw):
    return subprocess.run(args, check=True, **kw)
for f in ("enumerate_canon", "farbank"):
    run(["g++", "-O3", "-std=c++20", str(root / (f + ".cpp")), "-o", str(out / f)])
with (out / "stats.txt").open("w") as log:
    run([str(out / "enumerate_canon"), p], cwd=out, stdout=log)
opens = (out / "open.txt").read_text().splitlines()
assert len(opens) == 112
pumps = {int(row[0]): row for row in map(json.loads, (root / "round5-pumps.jsonl").read_text().splitlines())}
assert len(pumps) == 7
for i, row in pumps.items():
    assert opens[i].replace("_", "") == row[1]
with (out / "far5.txt").open("w") as log, (out / "far.log").open("w") as err:
    run([str(out / "farbank"), "5"], input="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens)), text=True, cwd=out, stdout=log, stderr=err)
far_ids = {int(x.split()[0]) for x in (out / "far5.txt").read_text().splitlines()}
assert len(far_ids) == 103
late = (root / "round5-late.txt").read_text()
late_ids = {opens.index(row.split()[0]) for row in late.splitlines()}
assert len(late_ids) == 2
assert far_ids.isdisjoint(pumps) and far_ids.isdisjoint(late_ids) and pumps.keys().isdisjoint(late_ids)
assert far_ids | pumps.keys() | late_ids == set(range(112))
(out / "late.txt").write_text(late)
(out / "proven.txt").write_text("".join(f"{opens[i]} BB6.Agent19Raw40.Round5.Leaf{i}\n" for i in sorted(pumps)))
src = (root / "certify_canonical.py").read_text()
anchor = "if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src = src.replace(anchor, anchor + "\nif any('.Round5.' in v for v in proven.values()):imports+='import Raw40Round5Pump\\n'")
sys.argv = [str(root / "certify_canonical.py"), str(out), str(out / "shards"), p, "1891", "Raw40C0LA0LB", "96"]
os.environ["RAW40_STANDALONE"] = "1"
exec(compile(src, sys.argv[0], "exec"), {"__file__": sys.argv[0], "__name__": "__main__"})
