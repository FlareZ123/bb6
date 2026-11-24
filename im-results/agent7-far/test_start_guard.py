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
    loaded = {}
    for name in ("generate_four_hole", "generate_four_hole_sibling"):
        path = AGENT31 / f"{name}.py"
        spec = importlib.util.spec_from_file_location(f"guard_test_{name}", path)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"cannot load {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        loaded[name] = module
        table = module.parse(module.PARENT)
        try:
            module.masks(table, 0, [1, 1])
        except AssertionError as exc:
            if "blank-start loop" not in repr(exc):
                raise
        else:
            raise AssertionError(f"{name} accepted DFA [1, 1] with start state 0")
    print("PASS: all five FAR emitters reject non-blank-preserving start DFAs")

    # The 14 candidate DFA strings are mirrored in an invalid scratch Lean
    # module. Its Cxx.fastValid pxx assertions are known false; this test
    # checks only candidate/key metadata, never destination validity.
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
            rf"def p{ident} : PartialMachine := fromCodes \[([^\]]+)\]", cert
        )
        dm = re.search(
            rf"def C{ident} : Data \d+ := \{{\s*start := [^\n]+\n\s*dfa := \[([^\]]+)\]",
            cert,
        )
        if pm is None or dm is None:
            raise AssertionError(f"missing p{ident}/C{ident} in Lean certificate source")
        table = [int(x.strip()) for x in pm.group(1).split(",")]
        dfa = "".join(
            x for x in re.findall(r"⟨(\d+),", dm.group(1))
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
    print("PASS: 14 candidate strings map across historical keys; destination validity is not asserted")

    # Cross-check the Python saturation routine against a known accepted
    # start-preserving Lean certificate. CI separately compiles R4PairHits.lean.
    r4_path = ROOT / "im-results" / "agent7-far" / "R4PairHits.lean"
    r4_source = r4_path.read_text()
    pm = re.search(r"def r4_0ra : PartialMachine := fromCodes \[([^\]]+)\]", r4_source)
    dm = re.search(
        r"def r4_0ra_data : Data 6 := ⟨0,\[([^\]]+)\],\[([^\]]+)\],\[([^\]]+)\],(\d+)⟩",
        r4_source,
    )
    if pm is None or dm is None:
        raise AssertionError("could not parse known accepted r4_0ra certificate")
    if "theorem r4_0ra_valid : r4_0ra_data.fastValid r4_0ra = true := by decide" not in r4_source:
        raise AssertionError("R4PairHits no longer contains its Lean fastValid proof")
    r4_codes = [int(x.strip()) for x in pm.group(1).split(",")]
    r4_dfa = [int(x.strip()) for x in dm.group(1).split(",")]
    r4_masks0 = [int(x.strip()) for x in dm.group(2).split(",")]
    r4_masks1 = [int(x.strip()) for x in dm.group(3).split(",")]
    r4_z = int(dm.group(4))
    sibling_module = loaded["generate_four_hole_sibling"]
    r4_table = sibling_module.parse("_".join(token(x) for x in r4_codes))
    d, dfa, masks0, masks1, z = sibling_module.masks(r4_table, 0, r4_dfa)
    if (d, dfa, masks0, masks1, z) != (6, r4_dfa, r4_masks0, r4_masks1, r4_z):
        raise AssertionError("Python masks() disagrees with the known Lean-accepted r4_0ra Data")
    print("PASS: Python masks() reproduces the known Lean-accepted r4_0ra destination certificate")

if __name__ == "__main__":
    main()
