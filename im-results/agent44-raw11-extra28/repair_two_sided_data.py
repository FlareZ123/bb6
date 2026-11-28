#!/usr/bin/env python3
"""Repair legacy generated TwoSidedAutomata Data modules in frozen checkpoints.

Older row-split checkpoints emitted an equation-style `def table :
PartialMachine` without the PhaseTree openings required by current source
elaboration.  This rewrites only that table presentation into the equivalent
typed lambda/match form; transition actions are copied verbatim.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: repair_two_sided_data.py DATA.lean")
    path = Path(sys.argv[1])
    text = path.read_text(encoding="utf-8")

    if "def table : PartialMachine := fun s => match s.1.val, s.2 with" in text:
        print(f"already repaired: {path.name}")
        return

    start = text.find("def table : PartialMachine\n")
    if start < 0:
        raise ValueError("legacy table header not found")
    cert = text.find("def cert :", start)
    if cert < 0:
        raise ValueError("cert definition not found after table")
    block = text[start:cert]
    lines = block.splitlines()
    if lines[0] != "def table : PartialMachine":
        raise ValueError("unexpected table header")

    out = ["def table : PartialMachine := fun s => match s.1.val, s.2 with"]
    action_count = 0
    for line in lines[1:]:
        m = re.fullmatch(r"\s*\| \((\d+),(false|true)\) => (.+)", line)
        if m:
            out.append(f"  | {m.group(1)},{m.group(2)} => {m.group(3)}")
            action_count += 1
            continue
        if re.fullmatch(r"\s*\| _ => none", line):
            out.append("  | _,_ => none")
            continue
        if line.strip():
            raise ValueError(f"unexpected table equation: {line!r}")

    if action_count == 0 or out[-1] != "  | _,_ => none":
        raise ValueError("incomplete legacy table")

    patched = text[:start] + "\n".join(out) + "\n" + text[cert:]
    if not re.search(r"^import PhaseTree$", patched, re.M):
        patched = "import PhaseTree\n" + patched
    patched = patched.replace(
        "open BB6.Agent4Automata\n",
        "open BB6.Agent4Automata BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree\n",
        1,
    )
    path.write_text(patched, encoding="utf-8")
    print(f"repaired {path.name}: actions={action_count}", flush=True)


if __name__ == "__main__":
    main()
