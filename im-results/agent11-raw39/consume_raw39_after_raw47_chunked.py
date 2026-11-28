#!/usr/bin/env python3
"""Source-accept the serial global Canonical40 → Raw47 → Raw39 quotient.

This consumer requires an already source-accepted Raw47 Canonical39 delta
on the actual Canonical40 ancestor. It authenticates that exact predecessor,
then transports the independently accepted Raw39 whole-parent bound via
bounded-chunk Lean kernel replay into its closure. An original Lean source
bridge removes the Raw39 Cover, leaving exactly 38 residual Covers.
No independent Canonical39 roster counts are added or spliced.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "agent45-canonical38-raw39"))
import consume_after_raw47 as a45
from consume_raw39_after_canonical40 import accepted_parent, ALLOWED, sha
from consume_raw39_kernel_chunked import compile_stage_kernel, generated_bridge
from chunked_kernel_replay import relocate_chunked

c = a45.c
NAME = "BB6.Agent11Canonical38Raw47Raw39"
NAMES = [
    NAME + ".literal_parent_agreement",
    NAME + ".raw39_cover_at",
    NAME + ".count38",
    NAME + ".removed_raw39_absent",
    NAME + ".sound38_at",
    NAME + ".exact_at_champion_score",
]
MEMBERSHIP = [
    "BB6.Agent11Raw39Canonical40Membership.parent_present",
    "BB6.Agent11Raw39Canonical40Membership.distinct_from_raw47",
]
BRIDGE = [
    "BB6.Agent11Raw39Canonical40Bridge.literal_eq_source",
    "BB6.Agent11Raw39Canonical40Bridge.parent_unique_in_roster40",
    "BB6.Agent11Raw39Canonical40Bridge.weighted_cover",
    "BB6.Agent11Raw39Canonical40Bridge.cover_at_champion_threshold",
]


def restore_serial_predecessor(work, raw47_run):
    linked, _, _, report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, report)
    ready, _, ready_pin = c.extra.restore_ready(
        work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = a45.restore_canonical40(
        work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    prior39, pin39 = a45.restore_canonical39(
        work, linked, prior40, pin40, raw47_run)
    assert prior39["remaining_residual_count"] == 39
    assert prior39["exact_at_champion_score"] == (
        "BB6.Agent50Canonical39Raw47.exact_at_champion_score")
    return linked, prior39, pin39


def source_check(source, linked, evidence, names):
    root, profile = c.u.compile_one(source, linked, evidence, names)
    assert set(profile) == set(names), (set(profile), set(names))
    assert all(set(ax) <= ALLOWED for ax in profile.values()), profile
    return root, profile


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--canonical39-raw47-run-id", type=int, required=True)
    p.add_argument("--onele-run", type=int, default=46114235329)
    p.add_argument("--chunk-size", type=int, default=64)
    a = p.parse_args()
    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical38-raw47-raw39-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

    # Independent original-source proofs, each authenticated by its
    # producer's accepted Lean theorem and pinned artifact manifests.
    parent_linked, parent = accepted_parent(work / "raw39-parent", a.onele_run)
    assert parent["bound"] == 28311 and len(parent["producers"]) == 11
    linked, predecessor, predecessor_pin = restore_serial_predecessor(
        work / "predecessor", a.canonical39_raw47_run_id)
    assert predecessor["remaining_residual_count"] == 39

    # Import only the accepted Canonical40 membership lemma into the
    # specific Canonical39 predecessor; this is a source proof, not an index.
    generated = []
    m, p_m = source_check(HERE / "Raw39Canonical40Membership.lean",
                          linked, evidence, MEMBERSHIP)
    generated.append(m)

    # The next physical parent occurs once in the *actual* Raw47 successor;
    # use Agent45's source theorem, rather than guessing list positions.
    conditional_src, conditional_names = a45.generate_source(work)
    q, p_q = source_check(conditional_src, linked, evidence,
                          conditional_names)
    generated.append(q)

    # The genuinely different Raw39 source-object cone must never shadow
    # the accepted predecessor's named objects. Replay its kernel-checked
    # definitions into globally fresh names in bounded source chunks.
    tool = compile_stage_kernel(work, linked)
    report, staged_objects, selected = relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=linked, work=work / "raw39-kernel-replay",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A11Raw39Slice", tool=tool,
        comparator_batch=HERE / "CompareKernelImportsBatch.lean",
        chunk_size=a.chunk_size)
    assert report["complete"]
    assert "BB6.Agent11Raw39Closed.parent_bound" in selected
    (evidence / "kernel-plan.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    for file in sorted(staged_objects.glob("*.olean")):
        target = linked / file.name
        if target.exists():
            assert sha(target) == sha(file), file.name
        else:
            shutil.copy2(file, target)
            generated.append(file)

    # Import the staged source theorem by a new proof of literal table
    # equality. No externally suggested or unverified axiom is postulated.
    bridge_src = generated_bridge(work, report["staged_root"], selected)
    b, p_b = source_check(bridge_src, linked, evidence, BRIDGE)
    generated.append(b)

    # Finally source-check the theorem with only 38 remaining named Covers.
    z, p_z = source_check(
        HERE / "Raw39AfterRaw47Closed.lean", linked, evidence, NAMES)
    generated.append(z)

    hashes = {}
    for file in generated:
        target = objects / file.name
        if target.exists():
            assert sha(target) == sha(file), file.name
        else:
            shutil.copy2(file, target)
        hashes[target.name] = sha(target)
    assert z.name in hashes
    profile = {**p_m, **p_q, **p_b, **p_z}
    assert NAME + ".exact_at_champion_score" in profile
    source_rev = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip()
    receipt = {
        "status": "source-accepted serial Raw47 and Raw39 successor of Canonical40",
        "source_revision": source_rev,
        "previous_delta": predecessor_pin,
        "previous_root_sha256": predecessor["root_sha256"],
        "previous_residual_count": 39,
        "remaining_residual_count": 38,
        "conditional_ancestor": a45.TARGET_NS,
        "whole_raw39_parent_source": parent,
        "raw39_olean_replay": {
            "mode": report["mode"],
            "source_modules": report["source_modules"],
            "affected_modules": report["affected_modules"],
            "selected_declarations": report["selected_declarations"],
            "kernel_comparison": report["kernel_comparison"],
            "chunks": len(report["chunks"]),
            "staged_root": report["staged_root"],
        },
        "axioms": profile,
        "root": z.name,
        "root_sha256": hashes[z.name],
        "delta_objects": hashes,
        "exact_at_champion_score": NAME + ".exact_at_champion_score",
        "onele_run": a.onele_run,
        "canonical39_raw47_run_id": a.canonical39_raw47_run_id,
    }
    (delta / "delta.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("PASS: accepted Raw47 Canonical39 consumed by complete Raw39; "
          "exactly 38 residual source-certified quotient obligations",
          flush=True)


if __name__ == "__main__":
    main()
