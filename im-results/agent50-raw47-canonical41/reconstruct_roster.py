#!/usr/bin/env python3
"""Reconstruct raw-index candidates of the accepted Canonical40 quotient roster.

This is an independent manifest-index audit, NOT a Lean theorem or substitute
for the source-accepted Canonical40 delta / Raw47 membership proof.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = HERE.parent / "agent13-roster-convergence" / "canonical-124.json"
# Exactly the eighteen already-consumed initial parents in the pinned
# canonical78 source index (see agent19-hard-root-crosswalk/crosswalk.cjs).
BASE_EXCLUSIONS = (66, 70, 80, 86, 87, 88, 91, 92, 93, 97, 98,
                   100, 101, 102, 104, 68, 72, 82)
# Follow the independently source-accepted parent-removal order. The final
# 'Canonical39-PROPOSED' is intentionally NOT an accepted source theorem.
STAGES = (
    ("Canonical78", BASE_EXCLUSIONS, 78),
    ("Canonical76", (107, 114), 76),
    ("Canonical68", (60, 109, 110, 111, 117, 121, 123, 125), 68),
    ("Canonical65", (71, 77, 81), 65),
    ("Canonical64", (120,), 64),
    ("Canonical59", (119, 115, 58, 108, 118), 59),
    ("Canonical58", (113,), 58),
    ("Canonical57", (124,), 57),
    ("Canonical53", (95, 99, 103, 105), 53),
    ("Canonical46", (83, 85, 69, 73, 78, 106, 79), 46),
    ("Canonical41", (63, 61, 67, 59, 122), 41),
    ("Canonical40", (57,), 40),
    ("Canonical39-PROPOSED", (47,), 39),
)
def first_use_canonical(entry):
    introduced = 2  # A=0, B=1 are already named in first-one normal form
    for step in entry["address"]:
        target = "ABCDEF".index(step["move"][2])
        if target > introduced:
            return False
        introduced = max(introduced, target + 1)
    return True

def reconstruct():
    data = json.loads(MANIFEST.read_text())
    assert len(data["entries"]) == 124
    entries = [e for e in data["entries"] if first_use_canonical(e)]
    assert len(entries) == 96
    assert len({e["raw_residual_index"] for e in entries}) == 96
    by_stage = []
    for name, removed, expected in STAGES:
        assert len(removed) == len(set(removed)), name
        available = {e["raw_residual_index"] for e in entries}
        assert set(removed) <= available, (name, set(removed)-available)
        entries = [e for e in entries
                   if e["raw_residual_index"] not in removed]
        assert len(entries) == expected, (name, len(entries), expected)
        by_stage.append((name, len(entries),
                         [e["raw_residual_index"] for e in entries]))
    # Independent source-manifest crosscheck: all 15 named original hard roots
    # must still have a containing raw representative in Canonical40.
    hard = json.loads((HERE.parent / "agent19-hard-root-crosswalk" /
                       "crosswalk.json").read_text())
    current40 = set(next(ids for name, _, ids in by_stage
                         if name == "Canonical40"))
    assert len(hard["records"]) == 15
    assert all(record["parent"]["raw"] in current40
               for record in hard["records"])
    return by_stage

if __name__ == "__main__":
    for name, n, ids in reconstruct():
        print(f"{name}: {n} retained raw indices")
        if name in ("Canonical40", "Canonical39-PROPOSED"):
            print(" ".join(map(str, ids)))
