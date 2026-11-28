#!/usr/bin/env python3
"""Source/kernel audit of Raw43 membership and conditional removal from accepted Canonical40."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent50-raw47-canonical41"))
import consume_after_canonical40 as ca

c = ca.c
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MEMBERSHIP = ["BB6.Agent25Raw43Canonical40Membership.parent_present"]
CONDITIONAL = [
    "BB6.Agent25Raw43Canonical40Conditional.parent_count40",
    "BB6.Agent25Raw43Canonical40Conditional.parent_root",
    "BB6.Agent25Raw43Canonical40Conditional.parents_pairwise_distinct",
    "BB6.Agent25Raw43Canonical40Conditional.parents_root",
    "BB6.Agent25Raw43Canonical40Conditional.count39",
    "BB6.Agent25Raw43Canonical40Conditional.removed_parent_absent",
    "BB6.Agent25Raw43Canonical40Conditional.conditional_sound",
    "BB6.Agent25Raw43Canonical40Conditional.conditional_exact_at_champion",
]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--conditional", action="store_true")
    a = ap.parse_args()
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = ca.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    assert prior40["exact_at_champion_score"] == "BB6.Agent31Canonical40Extra57.exact_at_champion_score"

    root, profiles = c.u.compile_one(
        HERE / "Raw43Canonical40Membership.lean", linked, evidence, MEMBERSHIP)
    assert set(profiles) == set(MEMBERSHIP), profiles
    assert all(set(ax) <= ALLOWED for ax in profiles.values())
    shutil.copy2(root, evidence / root.name)

    receipt = {
        "claim": "source-accepted literal Raw43 unique membership in Canonical40",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip(),
        "predecessor": pin40,
        "theorems": MEMBERSHIP,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": c.a68.sha(root),
    }

    if a.conditional:
        root2, profiles2 = c.u.compile_one(
            HERE / "Raw43Canonical40Conditional.lean", linked, evidence, CONDITIONAL)
        assert set(profiles2) == set(CONDITIONAL), profiles2
        assert all(set(ax) <= ALLOWED for ax in profiles2.values())
        shutil.copy2(root2, evidence / root2.name)
        receipt.update({
            "claim": "accepted Canonical40 to conditional 39+Raw43 exact source theorem",
            "conditional_theorems": CONDITIONAL,
            "conditional_axioms": profiles2,
            "conditional_root": root2.name,
            "conditional_root_sha256": c.a68.sha(root2),
        })

    (evidence / "membership.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("PASS: exact Canonical40 Raw43 membership" +
          (" and conditional 39-roster theorem" if a.conditional else ""), flush=True)

if __name__ == "__main__":
    main()
