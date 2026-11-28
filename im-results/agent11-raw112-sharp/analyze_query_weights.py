#!/usr/bin/env python3
"""Reproducible *untrusted* exact-weight candidate for the Raw112 six-hole audit.

The accepted source proof establishes partialCheck 100000 on a tree generated
from enumerate_fast.cpp and symbolic.py. This lightweight calculation extracts
the six unusually late .last leaves recorded in that exact pinned generator,
and computes possibleDelays using the same finite simple zero-edge graph as
SparseBlankDelay.lean. It is candidate discovery, NOT a replacement for Lean
partialWeights/partialScore checks or an attaining theorem.
"""
from __future__ import annotations

import hashlib
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "agent47-raw112-cut"
HARD_SHA256 = "23805b6953da558d904471078a742f87767945ec835afd5ebe602fbb68d32f69"
PARENT = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"

def hard_tables() -> list[str]:
    with tarfile.open(ROOT / "inductive-generators.tar.xz", "r:xz") as tf:
        items = [x for x in tf if x.name == "hard.txt"]
        if len(items) != 1:
            raise ValueError("missing or ambiguous hard.txt inside source-pinned archive")
        raw = tf.extractfile(items[0]).read()
    if hashlib.sha256(raw).hexdigest() != HARD_SHA256:
        raise ValueError("hard-table source bank did not match pinned digest")
    rows = raw.decode("utf-8").splitlines()
    if len(rows) != 131 or len(rows) != len(set(rows)):
        raise ValueError("wrong number of source residual hard rows")
    return rows

def zero_targets(p: str) -> list[set[int]]:
    """Return possible zero-writing successor states from each state q."""
    a = p.replace("_", "")
    if len(a) != 36:
        raise ValueError("partial table not 12 x 3")
    out = []
    for q in range(6):
        row = a[6*q:6*q+3]  # zero-read transition of state q
        if row == "---":
            out.append(set(range(6)))
        elif row in ("HHH", "H--") or row[0] == "1":
            out.append(set())
        elif row[0] == "0" and row[1] in "LR" and row[2] in "ABCDEF":
            out.append({ord(row[2]) - ord("A")})
        else:
            raise ValueError(f"invalid zero-row: q={q} {row}")
    return out

def possible_delays_and_path(partial: str, hole_slot: int) -> tuple[int, list[str]]:
    a = list(partial.replace("_", ""))
    if len(a) != 36 or a[hole_slot*3:hole_slot*3+3] != ["-","-","-"]:
        raise ValueError(f"not a one-hole first query at slot {hole_slot}")
    # refine p hole none: assign the query slot HALT, terminating zero paths.
    a[hole_slot*3:hole_slot*3+3] = ["H","H","H"]
    targets = zero_targets("".join(a))
    best_path: list[int] = [0]
    def visit(t: int, seen: int, suffix: list[int]) -> None:
        nonlocal best_path
        if len(suffix) > len(best_path):
            best_path = suffix[:]
        for q in range(6):
            if not (seen & (1 << q)) and t in targets[q]:
                visit(q, seen | (1 << q), [q, *suffix])
    visit(0, 1, [0])
    return len(best_path)-1, [chr(ord("A")+q) for q in best_path]

def main() -> None:
    hard = hard_tables()
    leaves = []
    for raw in (ROOT / "late.txt").read_text().splitlines():
        i, n, slot = map(int, raw.split())
        p = hard[i]
        if p.count("---") != 1:
            raise ValueError(f"late row {i} is not exactly one hole")
        delay, path = possible_delays_and_path(p, slot)
        leaves.append({
            "hard_index":i, "partial_table":p, "first_hole_steps":n,
            "slot":slot, "max_incoming_blank_delay":delay,
            "zero_path_to_A":path, "weighted_score":n+delay+1,
            "one_hole_halt_completion":p.replace("---", "HHH"),
        })
    if len(leaves) != 6 or set(v["hard_index"] for v in leaves) != {11,12,13,16,22,98}:
        raise ValueError("pinned six late leaves do not match source list")
    other_upper = 1000+6  # enumerate_fast.cpp has constexpr L=1000
    winner = max(leaves, key=lambda x:x["weighted_score"])
    if winner["weighted_score"] <= other_upper:
        raise ValueError("late maximum did not exceed initial audit cap")
    print(json.dumps({
        "source_parent":PARENT,
        "hard_sha256":HARD_SHA256,
        "base_audit_ceiling_bound":other_upper,
        "late_leaves":leaves,
        "candidate_global_weighted_score":winner["weighted_score"],
        "winning_hard_index":winner["hard_index"],
        "warning":"Candidate only; complete original-source Lean partialScore and witness check required",
    }, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
