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
    ap.add_argument("--conditional", action="store_true")
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

    if a.conditional:
        names = [
            "BB6.Agent11Raw39Canonical40Conditional.parent_count40",
            "BB6.Agent11Raw39Canonical40Conditional.parent_root",
            "BB6.Agent11Raw39Canonical40Conditional.parents_pairwise_distinct",
            "BB6.Agent11Raw39Canonical40Conditional.parents_root",
            "BB6.Agent11Raw39Canonical40Conditional.count39",
            "BB6.Agent11Raw39Canonical40Conditional.removed_parent_absent",
            "BB6.Agent11Raw39Canonical40Conditional.conditional_sound",
            "BB6.Agent11Raw39Canonical40Conditional.conditional_exact_at_champion",
        ]
        source2 = HERE / "Raw39Canonical40Conditional.lean"
        root2, proof_profiles = c.u.compile_one(source2, linked, evidence, names)
        assert set(proof_profiles) == set(names), proof_profiles
        assert all(set(ax) <= ALLOWED for ax in proof_profiles.values())
        shutil.copy2(root2, evidence / root2.name)
        receipt["claim"] = (
            "accepted Canonical40 to conditional 39+Raw39 exact source theorem"
        )
        receipt["conditional_theorems"] = names
        receipt["conditional_axioms"] = proof_profiles
        receipt["conditional_root"] = root2.name
        receipt["conditional_root_sha256"] = c.a68.sha(root2)
        (evidence / "membership.json").write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n")
        print("PASS: Canonical40 source theorem with one explicit Raw39 premise and 39 remaining Covers", flush=True)
        # Stronger algebraic consequence: at any larger threshold, parent
        # Cover can be consumed directly, rather than at floor 6,766,859.
        loose=[
            "BB6.Agent11Raw39Canonical40LooseThreshold.parents_cover_at",
            "BB6.Agent11Raw39Canonical40LooseThreshold.sound_at",
            "BB6.Agent11Raw39Canonical40LooseThreshold.exact_at_target",
            "BB6.Agent11Raw39Canonical40LooseThreshold.exact_at_champion",
        ]
        source3=HERE/"Raw39Canonical40LooseThreshold.lean"
        root3,loose_profiles=c.u.compile_one(source3,linked,evidence,loose)
        assert set(loose_profiles)==set(loose),loose_profiles
        assert all(set(ax)<=ALLOWED for ax in loose_profiles.values())
        shutil.copy2(root3,evidence/root3.name)
        receipt["loose_threshold_claim"]="target-score parent Cover suffices; local floor not required"
        receipt["loose_threshold_theorems"]=loose
        receipt["loose_threshold_axioms"]=loose_profiles
        receipt["loose_threshold_root_sha256"]=c.a68.sha(root3)
        (evidence/"membership.json").write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
        print("PASS: Canonical40 soundness at any target threshold ≥6766859; exactness from parent Cover at target",flush=True)

if __name__ == "__main__":
    main()
