#!/usr/bin/env python3
"""Compose the exact 22-way C1 partition from dependency-closed branch proofs.

This generator does not assume that a branch candidate bound is correct.
Every nonzero branch must supply its generated, kernel-checked sourceBound
theorem, at the exact domain and bound recorded here.
"""
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
CODES = (0, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24)
B = 3142249368711030


def generate():
    cfg = json.loads((HERE / "branches.json").read_text())
    bounds = {int(c): record["bound"] for c, record in cfg.items()}
    if set(bounds) != set(CODES) - {0, 2, 10}:
        raise ValueError("incomplete or unexpected nonlegacy branch roster")
    bounds.update({0: 8, 2: 3592, 10: 378})
    if max(bounds.values()) != B or bounds[9] != B:
        raise ValueError("candidate maximum changed; update the source lower witness and parent theorem")

    lines = ["import Box3Parent"] + [
        f"import Box3C{c}Closure" for c in CODES if c
    ]
    lines += [
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "namespace BB6.Agent13.Box3Parent",
        "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge",
        "",
        "theorem allBranches : ∀ c ∈ codes, ∀ m,",
        f"    Fits (branchDomain c) m → WeightedBound {B} m := by",
        "  intro c hc",
        "  have h : " + " ∨ ".join(f"c = {c}" for c in CODES) + " := by",
        "    simpa [codes] using hc",
        "  rcases h with " + " | ".join(["rfl"] * len(CODES)),
    ]
    for c in CODES:
        if c == 0:
            lines += [
                "  · intro m hm k d hk hd",
                f"    exact Nat.le_trans (c0_bound m hm k d hk hd) (by decide : 8 ≤ {B})",
            ]
        else:
            ns = f"BB6.Agent13.Box3C{c}"
            lines += [
                "  · intro m hm k d hk hd",
                f"    change Fits {ns}.sourceDomain m at hm",
                f"    exact Nat.le_trans ({ns}.sourceBound m hm k d hk hd) (by decide : {bounds[c]} ≤ {B})",
            ]
    lines += [
        "",
        f"theorem sourceBound : ∀ m, Fits raw10Remainder[3]! m → WeightedBound {B} m :=",
        f"  parent_upper {B} allBranches",
        "",
        "theorem sourceExact (N : Nat) :",
        f"    (∀ m, Fits raw10Remainder[3]! m → WeightedBound N m) ↔ {B} ≤ N :=",
        "  parent_exact_if_branches allBranches N",
        "",
        "#print axioms sourceBound",
        "#print axioms sourceExact",
        "end BB6.Agent13.Box3Parent",
        "",
    ]
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(generate(), encoding="utf-8")
