#!/usr/bin/env python3
"""Generate the Raw40 0LB_0RC five-hole candidate, with no unresolved leaves."""
import os, pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
out = root / "round3" / "0LB_0RC"
out.mkdir(parents=True, exist_ok=True)
p = "1RB0LB_1RC0RC_0RD---_1LD1LA_------_------"
def run(args, **kw):
    return subprocess.run(args, check=True, **kw)
for f in ("enumerate_canon", "farbank"):
    run(["g++", "-O3", "-std=c++20", str(root / (f + ".cpp")), "-o", str(out / f)])
with (out / "stats.txt").open("w") as log:
    run([str(out / "enumerate_canon"), p], cwd=out, stdout=log)
opens = (out / "open.txt").read_text().splitlines()
assert len(opens) == 172
def far(inp, size, filename):
    with (out / filename).open("w") as log, (out / (filename + ".log")).open("w") as err:
        run([str(out / "farbank"), str(size)], input=inp, text=True, cwd=out, stdout=log, stderr=err)
    return {int(x.split()[0]) for x in (out / filename).read_text().splitlines()}
def inp(ids):
    return "".join(f"{i} {opens[i].replace('_','')}\n" for i in ids)
all_ids = set(range(len(opens)))
far5 = far(inp(sorted(all_ids)), 5, "far5.txt")
assert len(far5) == 166
far6 = far(inp(sorted(all_ids - far5)), 6, "far_extra.txt")
assert all_ids - far5 - far6 == {4}
assert opens[4].replace("_","") == "1RB0LB1RC0RC0RD0LE1LD1LA1LC0LF1LA---"
(out / "proven.txt").write_text(opens[4] + " BB6.Agent19Raw40.Round3.Leaf4\n")
# Work with a transient modified generator, preserving existing generator behavior.
src = (root / "certify_canonical.py").read_text()
anchor = "if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src = src.replace(anchor, anchor + "\nif any('.Round3.' in v for v in proven.values()):imports+='import Raw40Round3Pump\\n'")
# The generator locates certify_shards.py relative to __file__.
sys.argv = [str(root / "certify_canonical.py"), str(out), str(out / "shards"), p, "746", "Raw40C0LB0RC", "96"]
os.environ["RAW40_STANDALONE"] = "1"
exec(compile(src, sys.argv[0], "exec"), {"__file__": sys.argv[0], "__name__": "__main__"})
