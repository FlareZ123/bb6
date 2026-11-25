#!/usr/bin/env python3
from pathlib import Path
import re

root = Path(__file__).resolve().parent / "out-oneLD"
log = Path("/tmp/a31-oneLD.log").read_text()
allowed = {"propext", "Classical.choice", "Quot.sound"}
names = ["BB6.Agent31OneLD.checked", "BB6.Agent31OneLD.all_completions_weighted"]
for p in root.glob("pump-*.json"):
    i = p.stem.split("-")[1]
    names.extend([f"BB6.Agent31OneLD.H{i}.growth", f"BB6.Agent31OneLD.H{i}.never"])
for name in names:
    m = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log, re.S)
    if not m:
        if "'" + name + "' does not depend on any axioms" in log:
            used = set()
        else:
            raise SystemExit("missing axiom audit: " + name)
    else:
        used = {x.strip() for x in m.group(1).split(",") if x.strip()}
    if not used <= allowed:
        raise SystemExit(f"nonstandard axioms in {name}: {used-allowed}")
print("all source theorem axiom profiles are standard")
