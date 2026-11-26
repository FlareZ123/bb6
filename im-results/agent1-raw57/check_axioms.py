#!/usr/bin/env python3
"""Reject nonstandard axioms and proof holes in a Raw57 Lean source-check log."""
from __future__ import annotations

import argparse
import re
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    parser.add_argument("--require", action="append", default=[])
    args = parser.parse_args()
    text = args.log.read_text(encoding="utf-8", errors="replace")
    forbidden = [name for name in ("sorryAx", "native_decide") if name in text]
    if forbidden:
        raise SystemExit(f"forbidden proof mechanism(s) in {args.log}: {forbidden}")
    lines = [line for line in text.splitlines() if "depends on axioms:" in line]
    if not lines:
        raise SystemExit(f"no '#print axioms' output found in {args.log}")
    checked = []
    for line in lines:
        match = re.search(r"depends on axioms:\s*\[([^]]*)\]", line)
        if match is None:
            raise SystemExit(f"could not parse axiom profile: {line}")
        axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
        extra = axioms - ALLOWED
        if extra:
            raise SystemExit(f"nonstandard axioms {sorted(extra)} in: {line}")
        checked.append(line)
    for required in args.require:
        if not any(required in line for line in checked):
            raise SystemExit(f"required theorem axiom profile not found: {required}")
    print(
        f"[raw57-axiom-gate] accepted {len(checked)} theorem profiles; "
        f"allowed={sorted(ALLOWED)}; required={args.require}",
        flush=True,
    )

if __name__ == "__main__":
    main()
