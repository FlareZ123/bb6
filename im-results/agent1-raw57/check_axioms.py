#!/usr/bin/env python3
"""Reject nonstandard axioms and proof holes in a Raw57 Lean source-check log."""
from __future__ import annotations

import argparse
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MARKER = "depends on axioms:"


def parse_axiom_profiles(text: str) -> list[tuple[str, set[str]]]:
    """Parse Lean axiom reports, including profiles wrapped across log lines."""
    lines = text.splitlines()
    profiles: list[tuple[str, set[str]]] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        marker_at = line.find(MARKER)
        if marker_at < 0:
            i += 1
            continue
        declaration = line[:marker_at].strip()
        remainder = line[marker_at + len(MARKER):]
        if "[" not in remainder:
            raise ValueError(f"missing '[' in axiom profile for {declaration!r}")
        remainder = remainder.split("[", 1)[1]
        while "]" not in remainder:
            i += 1
            if i >= len(lines):
                raise ValueError(f"unterminated axiom profile for {declaration!r}")
            if MARKER in lines[i]:
                raise ValueError(f"new axiom profile began before {declaration!r} was closed")
            remainder += " " + lines[i].strip()
        raw_axioms = remainder.split("]", 1)[0]
        axioms = {item.strip() for item in raw_axioms.split(",") if item.strip()}
        profiles.append((declaration, axioms))
        i += 1
    return profiles


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    parser.add_argument("--require", action="append", default=[])
    args = parser.parse_args()
    text = args.log.read_text(encoding="utf-8", errors="replace")
    forbidden = [name for name in ("sorryAx", "native_decide") if name in text]
    if forbidden:
        raise SystemExit(f"forbidden proof mechanism(s) in {args.log}: {forbidden}")
    try:
        profiles = parse_axiom_profiles(text)
    except ValueError as error:
        raise SystemExit(f"could not parse axiom profile: {error}") from error
    if not profiles:
        raise SystemExit(f"no '#print axioms' output found in {args.log}")
    for declaration, axioms in profiles:
        extra = axioms - ALLOWED
        if extra:
            raise SystemExit(
                f"nonstandard axioms {sorted(extra)} in {declaration}: {sorted(axioms)}"
            )
    for required in args.require:
        if not any(required in declaration for declaration, _ in profiles):
            raise SystemExit(f"required theorem axiom profile not found: {required}")
    print(
        f"[raw57-axiom-gate] accepted {len(profiles)} theorem profiles; "
        f"allowed={sorted(ALLOWED)}; required={args.require}",
        flush=True,
    )


if __name__ == "__main__":
    main()
