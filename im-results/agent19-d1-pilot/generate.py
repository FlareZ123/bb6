#!/usr/bin/env python3
"""Emit the source Lean cut for Raw47 from the deterministic cut.cpp JSON."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
tree = json.loads((ROOT / "Raw47-cut.json").read_text())
opens = (ROOT / "Raw47-open.txt").read_text().splitlines()
assert len(opens) == 114, len(opens)
NL = chr(10)

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
        assert len(children) == 24
        return f".split {n} {slot(s)} (byPartialMove [{NL}" + ("," + NL).join(emit(c) for c in children) + f"{NL}])"
    raise ValueError(k)

source = (ROOT / "Raw47Cut.template").read_text()
source = source.replace("@@TREE@@", emit(tree)).replace("@@OPEN_COUNT@@", str(len(opens)))
(ROOT / "Raw47Cut.lean").write_text(source)
