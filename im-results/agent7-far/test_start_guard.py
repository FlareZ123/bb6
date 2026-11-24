#!/usr/bin/env python3
"""Regression test for the blank-start loop condition in FAR candidate emitters."""
from __future__ import annotations
import ast
import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
AGENT31 = ROOT / "im-results" / "agent31-three-hole-tnf"
EMITTERS = {
    ROOT / "im-results" / "agent31-three-hole-tnf" / "generate_four_hole.py": "dfa",
    ROOT / "im-results" / "agent31-three-hole-tnf" / "generate_four_hole_sibling.py": "dfa",
    ROOT / "im-results" / "agent7-far" / "f1-siblings" / "emit.py": "D",
    ROOT / "im-results" / "agent7-far" / "wide132" / "emit.py": "D",
    ROOT / "im-results" / "agent7-far" / "wide133" / "emit.py": "D",
}

def main() -> None:
    for path, name in EMITTERS.items():
        source = path.read_text()
        tree = ast.parse(source, filename=str(path))
        masks = next(
            node for node in tree.body
            if isinstance(node, ast.FunctionDef) and node.name == "masks"
        )
        first = ast.unparse(masks.body[0])
        expected = f"{name}[0] != 0"
        if expected not in first or "raise AssertionError" not in first:
            raise AssertionError(f"{path}: missing first-statement guard {expected}")

    # Exercise both current four-hole generators on the concrete invalid
    # two-state DFA from the checker audit: delta(0, false) = 1.
    sys.path.insert(0, str(AGENT31))
    for name in ("generate_four_hole", "generate_four_hole_sibling"):
        path = AGENT31 / f"{name}.py"
        spec = importlib.util.spec_from_file_location(f"guard_test_{name}", path)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"cannot load {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        table = module.parse(module.PARENT)
        try:
            module.masks(table, 0, [1, 1])
        except AssertionError as exc:
            if "blank-start loop" not in repr(exc):
                raise
        else:
            raise AssertionError(f"{name} accepted DFA [1, 1] with start state 0")
    print("PASS: all five FAR emitters reject non-blank-preserving start DFAs")

if __name__ == "__main__":
    main()
