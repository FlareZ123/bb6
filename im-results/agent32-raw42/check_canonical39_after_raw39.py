#!/usr/bin/env python3
"""Authenticate accepted Raw39 Canonical39 and source-check the cumulative Raw42 39->38 cut."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
A11 = HERE.parent / "agent11-raw39"
A50 = HERE.parent / "agent50-raw47-canonical41"
sys.path.insert(0, str(A11))
sys.path.insert(0, str(A50))

from consume_raw39_after_canonical40 import canonical_source, accepted_parent, ALLOWED, sha
from consume_raw39_kernel_chunked import compile_stage_kernel, generated_bridge
from chunked_kernel_replay import relocate_chunked
import consume_after_canonical40 as ca

c = ca.c
RAW39_BRIDGE = [
    "BB6.Agent11Raw39Canonical40Bridge.literal_eq_source",
    "BB6.Agent11Raw39Canonical40Bridge.parent_unique_in_roster40",
    "BB6.Agent11Raw39Canonical40Bridge.weighted_cover",
    "BB6.Agent11Raw39Canonical40Bridge.cover_at_champion_threshold",
]
RAW39_SUCCESSOR = [
    "BB6.Agent11Raw39Canonical39Successor.count39",
    "BB6.Agent11Raw39Canonical39Successor.raw39_cover",
    "BB6.Agent11Raw39Canonical39Successor.sound_integrated",
    "BB6.Agent11Raw39Canonical39Successor.exact_at_champion_score",
]
RAW42_40 = ["BB6.Agent17Raw42Canonical40Membership.parent_present"]
RAW42_39 = ["BB6.Agent17Raw42Canonical39Membership.parent_present"]
RAW42_CUT = [
    "BB6.Agent17Raw42Canonical39Conditional.parent_count39",
    "BB6.Agent17Raw42Canonical39Conditional.count38",
    "BB6.Agent17Raw42Canonical39Conditional.removed_parent_absent",
    "BB6.Agent17Raw42Canonical39Conditional.conditional_sound",
    "BB6.Agent17Raw42Canonical39Conditional.conditional_exact_at_champion",
]
RAW42_FROM_NAMED = [
    "BB6.Agent17Raw42Canonical39FromNamed.literal_eq_p42",
    "BB6.Agent17Raw42Canonical39FromNamed.cover_from_named_at_global",
    "BB6.Agent17Raw42Canonical39FromNamed.sound_from_named",
]


def source_check(source, linked, evidence, names):
    root, profile = c.u.compile_one(source, linked, evidence, names)
    assert set(profile) == set(names), (set(profile), set(names))
    assert all(set(ax) <= ALLOWED for ax in profile.values()), profile
    return root, profile


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    a = ap.parse_args()

    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    canonical, predecessor = canonical_source(work / "canonical")
    parent_linked, parent = accepted_parent(work / "raw39-parent", a.onele_run)
    assert parent["bound"] == 28311 and len(parent["producers"]) == 11

    tool = compile_stage_kernel(work, canonical)
    report, staged_objects, names = relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=canonical,
        work=work / "raw39-staged",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A17Raw39Slice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=a.chunk_size,
    )
    assert report["complete"]
    assert "BB6.Agent11Raw39Closed.parent_bound" in names
    for f in sorted(staged_objects.glob("*.olean")):
        dest = canonical / f.name
        if dest.exists():
            assert sha(dest) == sha(f), f.name
        else:
            shutil.copy2(f, dest)

    bridge = generated_bridge(
        work, report["staged_root"], names,
        namespace="A17Raw39Slice",
        compatible=(report.get("mode") == "authenticated-original-compatible-link"))
    roots = {}
    profiles = {}
    for source, targets in [
        (bridge, RAW39_BRIDGE),
        (A11 / "Raw39Canonical39Successor.lean", RAW39_SUCCESSOR),
        (HERE / "Raw42Canonical40Membership.lean", RAW42_40),
        (HERE / "Raw42Canonical39Membership.lean", RAW42_39),
        (HERE / "Raw42Canonical39Conditional.lean", RAW42_CUT),
        (HERE / "Raw42Canonical39FromNamed.lean", RAW42_FROM_NAMED),
    ]:
        root, p = source_check(source, canonical, evidence, targets)
        roots[root.name] = sha(root)
        profiles.update(p)

    receipt = {
        "claim": "source-checked cumulative Raw42 conditional removal from accepted Raw39 Canonical39 lineage",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "accepted_predecessor": predecessor,
        "raw39_parent": parent,
        "raw39_transport_mode": report["mode"],
        "raw39_transport_affected_modules": report["affected_modules"],
        "remaining_residual_count_if_raw42_cover_supplied": 38,
        "theorems": profiles,
        "roots": roots,
    }
    (evidence / "raw42-after-raw39-conditional.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("PASS: accepted Raw39 Canonical39 lineage has Raw42 exactly once; conditional successor has 38 Covers", flush=True)


if __name__ == "__main__":
    main()
