#!/usr/bin/env python3
"""Directly join accepted Raw39 and Raw47 whole-parent proofs on Canonical40.

This path does not depend on either single-parent Canonical39 artifact. It
restores the exact accepted Canonical40 lineage, transports each independently
source-accepted parent proof through trust-level-zero kernel replay, checks the
already source-proved two-parent roster theorem, and emits one authenticated
40 -> 38 delta. The result remains conditional on Covers for the 38 survivors.
"""
import argparse
import json
import os
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

import consume_after_canonical40 as raw47
from consume_raw39_after_canonical40 import accepted_parent, ALLOWED, sha
from consume_raw39_kernel_chunked import compile_stage_kernel, generated_bridge
from chunked_kernel_replay import relocate_chunked

c = raw47.c
NS = "BB6.Agent3Canonical38Raw39Raw47Direct"
MEMBERSHIP = [
    "BB6.Agent11Raw39Canonical40Membership.parent_present",
    "BB6.Agent11Raw39Canonical40Membership.distinct_from_raw47",
]
CONDITIONAL = [
    "BB6.Agent11Raw39Canonical40Conditional.count39",
    "BB6.Agent11Raw39Canonical40Conditional.conditional_sound",
]
LOOSE = [
    "BB6.Agent11Raw39Canonical40LooseThreshold.remove_many_at",
]
BATCH = [
    "BB6.Agent11Raw39Raw47Batch38.parents_distinct",
    "BB6.Agent11Raw39Raw47Batch38.count38",
    "BB6.Agent11Raw39Raw47Batch38.raw39_removed",
    "BB6.Agent11Raw39Raw47Batch38.raw47_removed",
    "BB6.Agent11Raw39Raw47Batch38.sound38_at",
    "BB6.Agent11Raw39Raw47Batch38.exact38_at_champion",
]
RAW39_BRIDGE = [
    "BB6.Agent11Raw39Canonical40Bridge.literal_eq_source",
    "BB6.Agent11Raw39Canonical40Bridge.parent_unique_in_roster40",
    "BB6.Agent11Raw39Canonical40Bridge.weighted_cover",
    "BB6.Agent11Raw39Canonical40Bridge.cover_at_champion_threshold",
]
FINAL = [
    NS + ".raw39_cover_at_champion",
    NS + ".raw47_literal_agreement",
    NS + ".raw47_cover_at_champion",
    NS + ".sound38_at_champion",
    NS + ".exact_at_champion_score",
]


def source_check(source, linked, evidence, names):
    root, profile = c.u.compile_one(source, linked, evidence, names)
    if set(profile) != set(names):
        raise RuntimeError("missing axiom profiles: " + repr(set(names) - set(profile)))
    if not all(set(v) <= ALLOWED for v in profile.values()):
        raise RuntimeError("unapproved axiom profile: " + repr(profile))
    return root, profile


def restore_canonical40(work):
    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = raw47.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    assert prior40["exact_at_champion_score"] == (
        "BB6.Agent31Canonical40Extra57.exact_at_champion_score")
    return linked, prior40, pin40


def final_source(work):
    source = work / "Canonical38Raw39Raw47Direct.lean"
    source.write_text("""import Raw39Raw47Batch38
import Raw39Canonical40Bridge
import Raw47KernelBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Canonical38Raw39Raw47Direct

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p39 : PartialMachine := BB6.Agent11Raw39Raw47Batch38.p39
abbrev p47 : PartialMachine := BB6.Agent11Raw39Raw47Batch38.p47
noncomputable abbrev roster38 := BB6.Agent11Raw39Raw47Batch38.roster38

theorem raw39_cover_at_champion :
    Cover (WeightedBound (proposedTM63Moves + 7)) p39 := by
  simpa only [p39, BB6.Agent11Raw39Raw47Batch38.p39] using
    BB6.Agent11Raw39Canonical40Bridge.weighted_cover
      (proposedTM63Moves + 7) (by omega)

theorem raw47_literal_agreement :
    p47 = BB6.Agent50Raw47Bridge.parent :=
  sameTable_sound (by decide)

theorem raw47_cover_at_champion :
    Cover (WeightedBound (proposedTM63Moves + 7)) p47 := by
  rw [raw47_literal_agreement]
  exact BB6.Agent50Raw47Bridge.cover_at
    (proposedTM63Moves + 7) (by omega)

theorem sound38_at_champion :
    ∀ m, compatible root m →
      WeightedBound (proposedTM63Moves + 7) m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m :=
  BB6.Agent11Raw39Raw47Batch38.sound38_at
    (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    raw39_cover_at_champion raw47_cover_at_champion

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent11Raw39Raw47Batch38.exact38_at_champion
    raw39_cover_at_champion raw47_cover_at_champion hLeaves

#print axioms raw39_cover_at_champion
#print axioms raw47_literal_agreement
#print axioms raw47_cover_at_champion
#print axioms sound38_at_champion
#print axioms exact_at_champion_score

end BB6.Agent3Canonical38Raw39Raw47Direct
""")
    return source


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw47-run-id", type=int, default=46068688341)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical38-raw39-raw47-direct-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()
    generated = []
    profiles = {}

    linked, prior40, pin40 = restore_canonical40(work / "canonical")
    for source, names in (
        (A11 / "Raw39Canonical40Membership.lean", MEMBERSHIP),
        (A11 / "Raw39Canonical40Conditional.lean", CONDITIONAL),
        (A11 / "Raw39Canonical40LooseThreshold.lean", LOOSE),
        (A11 / "Raw39Raw47Batch38.lean", BATCH),
    ):
        root, ax = source_check(source, linked, evidence, names)
        generated.append(root)
        profiles.update(ax)

    # Transport the independently source-accepted Raw39 whole-parent theorem.
    parent_linked, raw39_parent = accepted_parent(
        work / "raw39-parent", args.onele_run)
    assert raw39_parent["bound"] == 28311
    assert len(raw39_parent["producers"]) == 11
    tool_work = work / "raw39-tool"
    tool_work.mkdir()
    tool = compile_stage_kernel(tool_work, linked)
    raw39_report, raw39_objects, selected = relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=linked,
        work=work / "raw39-kernel-replay",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A3Raw39Slice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=args.chunk_size,
    )
    assert raw39_report["complete"]
    assert "BB6.Agent11Raw39Closed.parent_bound" in selected
    for file in sorted(raw39_objects.glob("*.olean")):
        target = linked / file.name
        if target.exists():
            assert sha(target) == sha(file), file.name
        else:
            shutil.copy2(file, target)
            generated.append(target)
    raw39_bridge = generated_bridge(
        work, raw39_report["staged_root"], selected,
        namespace="A3Raw39Slice",
        compatible=(raw39_report.get("mode") ==
                    "authenticated-original-compatible-link"))
    root, ax = source_check(raw39_bridge, linked, evidence, RAW39_BRIDGE)
    generated.append(root)
    profiles.update(ax)

    # Transport Raw47 into the SAME authenticated Canonical40 environment.
    raw47_parent_dir = work / "raw47-parent"
    raw47_parent_dir.mkdir()
    raw47_spec, raw47_dirs = c.restore_parent(
        args.raw47_run_id, raw47_parent_dir, evidence)
    raw47_generated = []
    raw47_audit = {}
    raw47.kernel_replay_raw47(
        raw47_spec, raw47_dirs, linked, raw47_generated, raw47_audit,
        work, evidence, chunked=True)
    generated.extend(raw47_generated)

    source = final_source(work)
    root, ax = source_check(source, linked, evidence, FINAL)
    generated.append(root)
    profiles.update(ax)

    hashes = {}
    for file in generated:
        target = objects / file.name
        digest = sha(file)
        if target.exists():
            assert sha(target) == digest, file.name
        else:
            shutil.copy2(file, target)
        hashes[target.name] = digest

    receipt = {
        "status": (
            "source-accepted direct Raw39 plus Raw47 successor of Canonical40"),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "previous_delta": pin40,
        "previous_root_sha256": prior40["root_sha256"],
        "previous_residual_count": 40,
        "remaining_residual_count": 38,
        "raw39_parent": raw39_parent,
        "raw39_transport": {
            "mode": raw39_report["mode"],
            "source_modules": raw39_report["source_modules"],
            "affected_modules": raw39_report["affected_modules"],
            "selected_declarations": raw39_report["selected_declarations"],
            "kernel_comparison": raw39_report["kernel_comparison"],
            "chunks": len(raw39_report.get("chunks", [])),
            "staged_root": raw39_report["staged_root"],
        },
        "raw47_parent": raw47_spec,
        "raw47_link_audit": raw47_audit,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": hashes[root.name],
        "delta_objects": hashes,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "raw47_run_id": args.raw47_run_id,
        "onele_run": args.onele_run,
    }
    (delta / "delta.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw39 and Raw47 Covers jointly consumed from exact "
        "Canonical40; exactly 38 source-certified quotient obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
