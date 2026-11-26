#!/usr/bin/env python3
"""Emit the source Lean cut for Raw55 from the deterministic Raw49 classifier JSON."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
tree = json.loads((ROOT / "Raw55-cut.json").read_text())
opens = (ROOT / "Raw55-open.txt").read_text().splitlines()
tree_opens = []
counts = {}

def collect(t):
    tag = t[0]
    counts[tag] = counts.get(tag, 0) + 1
    if tag == "open":
        tree_opens.append(t[1])
    elif tag == "split":
        assert len(t[3]) == 24
        for child in t[3]:
            collect(child)

collect(tree)
assert tree_opens == opens, "tree/open manifest mismatch"
assert len(opens) == 274, len(opens)
assert counts.get("cycle") == 233 and counts.get("split") == 22
assert counts.get("alias", 0) == 0 and counts.get("last", 0) == 0

def slot(i):
    return f"({i // 2},{'true' if i % 2 else 'false'})"

def emit(t):
    k = t[0]
    if k in ("alias", "open"):
        return ".unresolved"
    if k == "cycle":
        return f".closed (.cycle {t[1]} {t[2]} {'true' if t[3] else 'false'} ({t[4]}))"
    if k == "last":
        return f".closed (.last {t[1]} {slot(t[2])})"
    if k == "split":
        n, s, children = t[1:]
        return f".split {n} {slot(s)} (byPartialMove [\n" + (",\n").join(emit(c) for c in children) + "\n])"
    raise ValueError(k)

source = (ROOT / "Raw55Cut.template").read_text()
source = source.replace("@@TREE@@", emit(tree)).replace("@@OPEN_COUNT@@", str(len(opens)))
(ROOT / "Raw55Cut.lean").write_text(source)
