#!/usr/bin/env python3
"""Split the authenticated Raw56 E1=1LB final proof by independent kernel checks.

This changes only proof compilation boundaries, NOT the audited theorem or
the two reductions. Lean imports all checked descendant modules, and verifies
each extracted declaration in the same original namespace and proof context.
"""
import argparse
import hashlib
from pathlib import Path

NS = "BB6.Agent4Raw56LB.E11LB"
NAME = "Raw56LBE11LBAll.lean"

def exactly_split(text, token):
    assert text.count(token) == 1, (token, text.count(token))
    return text.split(token, 1)

def split_parent(folder: Path):
    p = folder / "E11LB" / NAME
    original = p.read_text()
    assert original.count("theorem ctop :") == 1
    assert original.count("theorem nrtop :") == 1
    assert original.count("theorem partial_quotient :") == 1
    header, rest = exactly_split(original, "theorem qtop :")
    check, rest = exactly_split(rest, "theorem nrtop :")
    residual, rest = exactly_split(rest, "theorem partial_quotient :")
    final, trailer = exactly_split(rest, "#print axioms partial_quotient")
    assert trailer.strip() == f"end {NS}", trailer[:250]
    assert "theorem ctop :" in check and "theorem exact_residuals :" in residual
    assert "def residuals :" in residual and "theorem partial_quotient :" not in residual
    assert "abbrev ptop := p" in header
    ns_start = header.index(f"namespace {NS}")
    scope = header[ns_start:header.index("abbrev ptop := p", ns_start)]
    opts = "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    suffix = f"end {NS}\n"
    output = {
        "Raw56LBTopDefs.lean": header + "\n#check ttop\n" + suffix,
        "Raw56LBTopChecks.lean":
            "import Raw56LBTopDefs\n" + opts + scope
            + "theorem qtop :" + check + "\n#print axioms ctop\n" + suffix,
        "Raw56LBTopResiduals.lean":
            "import Raw56LBTopDefs\n" + opts + scope
            + "theorem nrtop :" + residual
            + "\n#print axioms exact_residuals\n" + suffix,
        NAME:
            "import Raw56LBTopChecks\nimport Raw56LBTopResiduals\n"
            + opts + scope + "theorem partial_quotient :" + final
            + "#print axioms partial_quotient\n" + suffix,
    }
    for name, content in output.items():
        assert content.count(f"end {NS}") == 1, name
        (p.parent / name).write_text(content)
        print("SPLIT", name, len(content), "bytes", hashlib.sha256(content.encode()).hexdigest(), flush=True)
    assert output[NAME].count("theorem partial_quotient :") == 1
    assert output["Raw56LBTopResiduals.lean"].count("theorem nrtop :") == 1
    print("ORIGINAL", NAME, len(original), hashlib.sha256(original.encode()).hexdigest(), flush=True)

def main():
    arg = argparse.ArgumentParser()
    arg.add_argument("--prep", type=Path, required=True)
    args = arg.parse_args()
    split_parent(args.prep)

if __name__ == "__main__":
    main()
