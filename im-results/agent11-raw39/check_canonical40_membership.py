#!/usr/bin/env python3
"""Original-source/kernel audit of Raw39's membership in the accepted Canonical40 roster.

The reconstructed raw-index crosswalk is only a candidate; the theorem in
Raw39Canonical40Membership.lean must be elaborated against the exact
source-accepted Canonical40Extra57 delta closure, with all ancestors restored
from their pinned accepted artifacts.
"""
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
CLAIMS = [
    "BB6.Agent11Raw39Canonical40Membership.parent_present",
    "BB6.Agent11Raw39Canonical40Membership.distinct_from_raw47",
]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    a = ap.parse_args()
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(
        work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = ca.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    assert prior40["exact_at_champion_score"] == (
        "BB6.Agent31Canonical40Extra57.exact_at_champion_score")

    source = HERE / "Raw39Canonical40Membership.lean"
    root, profiles = c.u.compile_one(source, linked, evidence, CLAIMS)
    assert set(profiles) == set(CLAIMS), profiles
    assert all(set(ax) <= ALLOWED for ax in profiles.values())
    shutil.copy2(root, evidence / root.name)
    receipt = {
        "claim": "source-accepted literal Raw39 unique membership in Canonical40",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip(),
        "predecessor": pin40,
        "theorems": CLAIMS,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": c.a68.sha(root),
    }
    (evidence / "membership.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("PASS: exact Canonical40 Raw39 membership and Raw47 distinction", flush=True)

if __name__ == "__main__":
    main()
