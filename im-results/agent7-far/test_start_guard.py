#!/usr/bin/env python3
"""Regression test for the blank-start loop condition in FAR candidate emitters."""
from __future__ import annotations
import ast
import importlib.util
import re
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

    # The 14 canonical DFA strings are already represented by Lean Data
    # objects for their actual raw85 destination tables. Their old lookup
    # keys are deliberately different: keys are candidate metadata only.
    bank_path = ROOT / "im-results" / "agent21-raw85" / "dfa-candidates.txt"
    cert_path = ROOT / "im-results" / "agent21-raw85" / "Raw85FARCertificates.lean"
    bank = [
        line.split() for line in bank_path.read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    cert = cert_path.read_text()
    if len(bank) != 14:
        raise AssertionError(f"expected 14 canonical candidates, found {len(bank)}")

    def token(code: int) -> str:
        if code == 24:
            return "---"
        return f"{(code >> 1) & 1}{'R' if code & 1 else 'L'}{'ABCDEF'[code >> 2]}"

    for i in range(14):
        ident = f"{i:02d}"
        pm = re.search(
            rf"def p{ident} : PartialMachine := fromCodes \\[([^\\]]+)\\]", cert
        )
        dm = re.search(
            rf"def C{ident} : Data \\d+ := \\{{\\s*start := [^\\n]+\\n\\s*dfa := \\[([^\\]]+)\\]",
            cert,
        )
        if pm is None or dm is None:
            raise AssertionError(f"missing p{ident}/C{ident} in Lean certificate source")
        table = [int(x.strip()) for x in pm.group(1).split(",")]
        dfa = "".join(
            x for x in re.findall(r"⟨(\\d+),", dm.group(1))
        )
        if not dfa:
            raise AssertionError(f"C{ident} has no parsed DFA")
        destination_key = [token(table[j]) for j in (5, 1, 8, 10)]
        matching = [row for row in bank if len(row) == 6 and row[5] == dfa]
        if not matching:
            raise AssertionError(f"C{ident} DFA is absent from dfa-candidates.txt")
        if any(row[:4] == destination_key for row in matching):
            raise AssertionError(
                f"C{ident}: expected historical candidate keys to differ from destination key"
            )
    print("PASS: all 14 Lean raw85 Data DFAs are reusable across different historical keys")

if __name__ == "__main__":
    main()
