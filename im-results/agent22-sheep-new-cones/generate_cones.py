#!/usr/bin/env python3
"""Generate source-import Lean cone barriers from exact arithmetic DAGs.

The generated Lean theorems discharge root membership and start exclusion;
universal reverse-closure arithmetic stays as explicit hypotheses.
"""
from pathlib import Path
from filelock import FileLock
import os
import tempfile

from certificate import CASES, exact_cone


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "ConeCertificateBridge.lean"


def main():
    source = [
        "import ConeCore", "",
        "namespace Agent22SheepCones", "",
        "/- Six source-level reachability barriers; reverse closure remains",
        "   an explicit mathematical premise requiring separate certification. -/",
        "",
    ]
    for J, P in CASES:
        nodes, edges = exact_cone(J)
        assert all(b <= 0 for s, b, d in nodes)
        clauses = [
            f"({d}*x+{-b} = 2^({J+s}+{P}*k))"
            for s, b, d in nodes
        ]
        source += [
            f"def Basin{J} (k x : Nat) : Prop :=",
            "  " + " ∨\n  ".join(clauses), "",
            f"theorem root_in_{J} (k : Nat) : Basin{J} k (2^({J}+{P}*k)) := by",
            f"  unfold Basin{J}", "  left", "  simp", "",
            f"theorem not_blank_{J} (k : Nat) : ¬ Basin{J} k 10 := by",
            "  intro h",
            "  change " + " ∨\n    ".join(
                clause.replace("x", "10") for clause in clauses
            ) + " at h",
            "  rcases h with " + " | ".join(
                f"h{i}" for i in range(len(nodes))
            ),
        ]
        for i, (shift, b, d) in enumerate(nodes):
            source.append(
                f"  · exact not_10_at_node ({J+shift}+{P}*k) 0 "
                f"{d} {-b} (by omega) (by decide) "
                f"(by simpa using h{i})"
            )
        source += [
            "",
            "/-- This theorem makes the unresolved reverse-closure"
            " obligation explicit. -/",
            f"theorem unreachable_{J}_if_reverse_closed (k : Nat)",
            f"    (hclosed : ∀ {{x y}}, SheepEven.EvenEdge x y → "
            f"Basin{J} k y → Basin{J} k x) :",
            f"    ¬ SheepEven.EvenReach 10 (2^({J}+{P}*k)) := by",
            f"  exact no_reach_if_reverse_closed "
            f"(root_in_{J} k) (not_blank_{J} k) hclosed",
            "",
            f"#print axioms unreachable_{J}_if_reverse_closed", "",
        ]
        print(f"Generated J={J} P={P}: {len(nodes)} nodes, {len(edges)} edges")
    source += ["end Agent22SheepCones", ""]
    content = "\n".join(source)
    with FileLock(str(OUTPUT) + ".lock"):
        fd, temp = tempfile.mkstemp(dir=ROOT, prefix="." + OUTPUT.name + ".")
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                handle.write(content)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp, OUTPUT)
        finally:
            if os.path.exists(temp):
                os.unlink(temp)
    print("Wrote", OUTPUT, len(content), "bytes")


if __name__ == "__main__":
    main()
