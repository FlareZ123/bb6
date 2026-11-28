#!/usr/bin/env python3
"""Consume accepted Raw39 after the exact Raw47 -> Raw112 global lineage.

This is a strict serial quotient consumer.  It authenticates:
  Canonical40 -> accepted Raw47 Canonical39 -> accepted Raw112 Canonical38,
then transports the independently accepted Raw39 whole-parent proof into that
exact object closure and removes Raw39 from the concrete 38-roster.

A successful run leaves 37 named Cover obligations.  Independent residual
counts are never added.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SIBLINGS = HERE.parent
sys.path.insert(0, str(SIBLINGS / "agent50-raw47-canonical41"))
sys.path.insert(0, str(SIBLINGS / "agent45-canonical38-raw39"))
sys.path.insert(0, str(SIBLINGS / "agent11-raw39"))

import consume as c
import consume_after_raw47 as a45
from consume_raw39_after_canonical40 import accepted_parent, ALLOWED, sha
from consume_raw39_kernel_chunked import compile_stage_kernel, generated_bridge
from chunked_kernel_replay import relocate_chunked

PREV_NS = "BB6.Agent33Canonical38Raw47Raw112"
TARGET_NS = "BB6.Agent17Canonical37Raw47Raw112Raw39"
ARTIFACT = "canonical38-raw47-raw112-thin-delta"

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
TARGETS = [
    TARGET_NS + ".parent_count38",
    TARGET_NS + ".count37",
    TARGET_NS + ".removed_raw39_absent",
    TARGET_NS + ".sound_integrated",
    TARGET_NS + ".exact_at_champion_score",
]


def restore_raw112_successor(work, linked, predecessor, predecessor_pin, run_id):
    run, item, pin = c.extra.artifact(run_id, ARTIFACT)
    folder = work / "canonical38-raw47-raw112"
    folder.mkdir()
    dirs = c.a68.download(pin, folder)
    metadata = folder / "metadata" / str(item["id"])
    matches = list(metadata.rglob("delta.json"))
    assert len(matches) == 1, matches
    report = json.loads(matches[0].read_text())
    assert report["status"] == "source-accepted Raw112 successor of Canonical39 Raw47"
    assert report["source_revision"] == run["head_sha"]
    assert report["previous_delta"] == predecessor_pin
    assert report["previous_root_sha256"] == predecessor["root_sha256"]
    assert report["previous_residual_count"] == 39
    assert report["remaining_residual_count"] == 38
    assert report["exact_at_champion_score"] == PREV_NS + ".exact_at_champion_score"
    assert report["exact_at_champion_score"] in report["axioms"]
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())

    objects = report["delta_objects"]
    observed = {}
    for directory in dirs:
        for file in directory.glob("*.olean"):
            if file.name in observed:
                assert sha(observed[file.name]) == sha(file), file.name
                continue
            observed[file.name] = file
    assert set(objects) == set(observed), (
        set(objects) - set(observed), set(observed) - set(objects))
    assert objects[report["root"]] == report["root_sha256"]
    for name, digest in objects.items():
        assert name == Path(name).name
        assert sha(observed[name]) == digest, name
        dest = linked / name
        if dest.exists():
            assert sha(dest) == digest, name
        else:
            shutil.copy2(observed[name], dest)
    return report, {
        "run_id": run_id,
        "artifact_id": item["id"],
        "artifact_sha256": pin[2],
        "root_sha256": report["root_sha256"],
    }


def restore_predecessor(work, raw47_run, raw112_successor_run):
    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(
        work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = a45.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    prior39, pin39 = a45.restore_canonical39(
        work, linked, prior40, pin40, raw47_run)
    assert prior39["remaining_residual_count"] == 39
    prior38, pin38 = restore_raw112_successor(
        work, linked, prior39, pin39, raw112_successor_run)
    assert prior38["remaining_residual_count"] == 38
    return linked, prior38, pin38


def source_check(source, linked, evidence, names):
    root, profile = c.u.compile_one(source, linked, evidence, names)
    assert set(profile) == set(names), (set(profile), set(names))
    assert all(set(ax) <= ALLOWED for ax in profile.values()), profile
    return root, profile


def target_source(work):
    source = work / "Canonical37Raw47Raw112Raw39.lean"
    source.write_text("""import Canonical38Raw47Raw112
import Raw39Canonical40Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Canonical37Raw47Raw112Raw39

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent33Canonical38Raw47Raw112.roster38
abbrev p39 : PartialMachine := BB6.Agent11Raw39Canonical40Bridge.p
abbrev removedParents : List PartialMachine := [p39]

theorem parent_count38 :
    (baseRoster.filter (fun e => sameTable e.2 p39)).length = 1 := by
  decide

theorem parent_root :
    p39 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p39 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p39 := by simpa [removedParents] using hp
  subst p
  exact BB6.Agent11Raw39Canonical40Bridge.cover_at_champion_threshold

noncomputable def roster37 := removeParents removedParents baseRoster

theorem count37 : roster37.length = 37 := by
  decide

theorem removed_raw39_absent :
    (roster37.filter (fun e => sameTable e.2 p39)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent33Canonical38Raw47Raw112.sound_integrated
    parents_root parents_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) := by
  apply exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    sound_integrated
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count38
#print axioms count37
#print axioms removed_raw39_absent
#print axioms sound_integrated
#print axioms exact_at_champion_score

end BB6.Agent17Canonical37Raw47Raw112Raw39
""")
    return source


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--canonical39-raw47-run-id", type=int, required=True)
    ap.add_argument("--canonical38-raw47-raw112-run-id", type=int, required=True)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical37-raw47-raw112-raw39-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

    parent_linked, parent = accepted_parent(work / "raw39-parent", args.onele_run)
    assert parent["bound"] == 28311 and len(parent["producers"]) == 11
    linked, predecessor, predecessor_pin = restore_predecessor(
        work / "predecessor",
        args.canonical39_raw47_run_id,
        args.canonical38_raw47_raw112_run_id)

    generated = []
    m, p_m = source_check(
        SIBLINGS / "agent11-raw39" / "Raw39Canonical40Membership.lean",
        linked, evidence, MEMBERSHIP)
    generated.append(m)

    tool = compile_stage_kernel(work, linked)
    report, staged_objects, selected = relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=linked,
        work=work / "raw39-kernel-replay",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A11Raw39Slice",
        tool=tool,
        comparator_batch=SIBLINGS / "agent11-raw39" / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=args.chunk_size)
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

    bridge_src = generated_bridge(
        work, report["staged_root"], selected,
        compatible=(report.get("mode") == "authenticated-original-compatible-link"))
    b, p_b = source_check(bridge_src, linked, evidence, BRIDGE)
    generated.append(b)

    target = target_source(work)
    z, p_z = source_check(target, linked, evidence, TARGETS)
    generated.append(z)

    hashes = {}
    for file in generated:
        dest = objects / file.name
        if dest.exists():
            assert sha(dest) == sha(file), file.name
        else:
            shutil.copy2(file, dest)
        hashes[dest.name] = sha(dest)

    profiles = {**p_m, **p_b, **p_z}
    receipt = {
        "status": "source-accepted serial Raw47, Raw112 and Raw39 successor of Canonical40",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "previous_delta": predecessor_pin,
        "previous_root_sha256": predecessor["root_sha256"],
        "previous_residual_count": 38,
        "remaining_residual_count": 37,
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
        "axioms": profiles,
        "root": z.name,
        "root_sha256": hashes[z.name],
        "delta_objects": hashes,
        "exact_at_champion_score": TARGET_NS + ".exact_at_champion_score",
        "onele_run": args.onele_run,
        "canonical39_raw47_run_id": args.canonical39_raw47_run_id,
        "canonical38_raw47_raw112_run_id":
            args.canonical38_raw47_raw112_run_id,
    }
    (delta / "delta.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("PASS: accepted Raw47 -> Raw112 -> Raw39 lineage leaves 37 Covers",
          flush=True)


if __name__ == "__main__":
    main()
