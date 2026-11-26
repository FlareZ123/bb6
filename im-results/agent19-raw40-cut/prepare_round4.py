#!/usr/bin/env python3
"""Regenerate the complete 0LA_1LB five-hole weighted bound proof."""
import json, os, pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
out = root / "round4" / "0LA_1LB"
out.mkdir(parents=True, exist_ok=True)
p = "1RB0LA_1RC1LB_0RD---_1LD1LA_------_------"
def run(args, **kw):
    return subprocess.run(args, check=True, **kw)
for f in ("enumerate_canon", "farbank"):
    run(["g++", "-O3", "-std=c++20", str(root / (f + ".cpp")), "-o", str(out / f)])
with (out / "stats.txt").open("w") as log:
    run([str(out / "enumerate_canon"), p], cwd=out, stdout=log)
opens = (out / "open.txt").read_text().splitlines()
assert len(opens) == 374
assert "maxscore=334 " in (out / "stats.txt").read_text()
pumps = {int(row[0]): row for row in map(json.loads, (root / "round4-pumps.jsonl").read_text().splitlines())}
assert len(pumps) == 25
for i, row in pumps.items():
    assert opens[i].replace("_", "") == row[1]
with (out / "far5.txt").open("w") as log, (out / "far.log").open("w") as err:
    run([str(out / "farbank"), "5"], input="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens)), text=True, cwd=out, stdout=log, stderr=err)
far_ids = {int(x.split()[0]) for x in (out / "far5.txt").read_text().splitlines()}
assert len(far_ids) == 349
assert far_ids.isdisjoint(pumps) and far_ids | pumps.keys() == set(range(374))
(out / "proven.txt").write_text("".join(f"{opens[i]} BB6.Agent19Raw40.Round4.Leaf{i}\n" for i in sorted(pumps)))
src = (root / "certify_canonical.py").read_text()
anchor = "if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src = src.replace(anchor, anchor + "\nif any('.Round4.' in v for v in proven.values()):imports+='import Raw40Round4Pump\\n'")
sys.argv = [str(root / "certify_canonical.py"), str(out), str(out / "shards"), p, "334", "Raw40C0LA1LB", "96"]
os.environ["RAW40_STANDALONE"] = "1"
exec(compile(src, sys.argv[0], "exec"), {"__file__": sys.argv[0], "__name__": "__main__"})
