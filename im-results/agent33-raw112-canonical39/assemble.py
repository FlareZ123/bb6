#!/usr/bin/env python3
"""Consume an accepted Raw112 parent directly on the accepted Canonical40 Raw57 boundary."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
sys.path.insert(0, str(REPO_ROOT / "im-results" / "agent2-ready-union"))
sys.path.insert(0, str(REPO_ROOT / "im-results" / "agent29-raw57-consumer"))
sys.path.insert(0, str(REPO_ROOT / "im-results" / "agent17-raw112-canonical58"))
sys.path.insert(0, str(REPO_ROOT / "im-results" / "agent31-shared-core"))

import extra_ready_union as extra
import resume_ready_union as resume
import consume_after_canonical41 as raw57
import assemble_canonical68 as a68
import assemble_canonical_selected as selected
from assemble_canonical58_raw112_graft import verify_raw112_parent

CANONICAL40_RUN = 46075158700
CANONICAL40_ARTIFACT = 15234886499
CANONICAL40_SHA = "d1547d32ca4668d250978f288c827287cadd425eef9c8e0c230802d313177207"
CANONICAL40_NS = "BB6.Agent31Canonical40Extra57"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"
NS = "BB6.Agent33Canonical39Raw112"


def restore_canonical40(work: Path, linked: Path, prior: dict, prior_pin: dict):
    run, item, pin = extra.artifact(CANONICAL40_RUN, "canonical40-raw57-thin-delta")
    assert item["id"] == CANONICAL40_ARTIFACT
    assert pin[2] == CANONICAL40_SHA
    dirs = a68.download(pin, work)
    metadata = work / "metadata" / str(item["id"])
    reports = list(metadata.rglob("delta.json"))
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["status"] == "source-accepted Raw57 successor of Canonical41"
    assert report["source_revision"] == run["head_sha"]
    assert report["previous_delta"] == prior_pin
    assert report["previous_root_sha256"] == prior["root_sha256"]
    assert report["previous_residual_count"] == 41
    assert report["remaining_residual_count"] == 40
    assert report["exact_at_champion_score"] == CANONICAL40_NS + ".exact_at_champion_score"
    assert report["exact_at_champion_score"] in report["axioms"]
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())

    objects = report["delta_objects"]
    observed = {}
    for d in dirs:
        for f in d.glob("*.olean"):
            if f.name in observed:
                assert a68.sha(observed[f.name]) == a68.sha(f), f.name
                continue
            observed[f.name] = f
    assert set(objects) == set(observed), (sorted(objects), sorted(observed))
    assert objects[report["root"]] == report["root_sha256"]
    for name, digest in objects.items():
        assert a68.sha(observed[name]) == digest, name
        dest = linked / name
        if dest.exists():
            assert a68.sha(dest) == digest, name
        else:
            shutil.copy2(observed[name], dest)

    return report, {
        "run_id": CANONICAL40_RUN,
        "artifact_id": item["id"],
        "artifact_sha256": pin[2],
        "root_sha256": report["root_sha256"],
    }


def generate(prior: dict, folder: Path):
    module = "Canonical39Raw112AfterCanonical40"
    source = folder / (module + ".lean")
    text = f"""import {Path(prior["root"]).stem}
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace {NS}

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster := {CANONICAL40_NS}.roster40
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent

theorem p112_count40 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by decide

theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent47Raw112.parent_root

theorem p112_cover : Cover (WeightedBound 6766859) p112 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by decide : 100000 ≤ 6766859)

abbrev parents : List PartialMachine := [p112]

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) parents := by decide

theorem parents_root :
    ∀ p ∈ parents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp [parents] at hp
  subst p
  exact p112_root

theorem parents_cover :
    ∀ p ∈ parents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp [parents] at hp
  subst p
  exact p112_cover

noncomputable def roster39 := removeParents parents baseRoster

theorem count39 : roster39.length = 39 := by decide

theorem raw112_removed :
    (roster39.filter (fun e => sameTable e.2 p112)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster39, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := parents)
    (roster := baseRoster)
    {CANONICAL40_NS}.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster39, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count40
#print axioms p112_cover
#print axioms parents_pairwise_distinct
#print axioms count39
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end {NS}
"""
    source.write_text(text)
    return source


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw112-run-id", type=int, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical39-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    generated = delta / "generated"
    for d in (evidence, objects, generated):
        d.mkdir(parents=True, exist_ok=True)

    linked, _, _, base_report = extra.base.verify_base(work, extra.base.BASE_RUN)
    sharp = resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = extra.restore_ready(work, linked, sharp, raw57.READY_RUN)
    canonical41, canonical41_pin = raw57.restore_extra(
        work / "canonical41", linked, ready, ready_pin
    )
    prior, prior_pin = restore_canonical40(
        work / "canonical40", linked, canonical41, canonical41_pin
    )

    raw112_work = work / "raw112"
    raw112_work.mkdir()
    raw112_meta, raw112_dirs, raw112_summary = verify_raw112_parent(
        raw112_work, args.raw112_run_id
    )

    before = set(linked.glob("*.olean"))
    audit = {}
    copied = []
    selected.add_family({"root": "Raw112ClosedCover"}, raw112_dirs, linked, copied, audit)
    assert (linked / "Raw112ClosedCover.olean").is_file()

    source = generate(prior, generated)
    env = dict(os.environ, LEAN_PATH=str(linked))
    output = linked / (source.stem + ".olean")
    log = a68.compile_module(source, output, env, work / "canonical39.log")
    names = [
        NS + ".p112_count40",
        NS + ".p112_cover",
        NS + ".parents_pairwise_distinct",
        NS + ".count39",
        NS + ".raw112_removed",
        NS + ".sound_integrated",
        NS + ".exact_at_target",
        NS + ".exact_at_champion_score",
    ]
    profiles = a68.gate(log, names)
    assert all(set(v) <= ALLOWED for v in profiles.values())

    new_objects = sorted((set(linked.glob("*.olean")) - before) | {output})
    hashes = {}
    for path in new_objects:
        dst = objects / path.name
        if not dst.exists():
            shutil.copy2(path, dst)
        hashes[dst.name] = a68.sha(dst)

    report = {
        "status": "source-accepted Canonical40-to-39 Raw112 delta",
        "canonical40_predecessor": prior_pin,
        "previous_root_sha256": prior["root_sha256"],
        "previous_residual_count": 40,
        "remaining_residual_count": 39,
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": raw112_meta["artifact_name"],
        "raw112_artifact_id": raw112_meta["artifact_id"],
        "raw112_artifact_sha256": raw112_meta["artifact_digest"],
        "raw112_parent_table": RAW112_TABLE,
        "raw112_parent_theorem": RAW112_THEOREM,
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": raw112_summary,
        "raw112_link_audit": audit,
        "root": output.name,
        "root_sha256": a68.sha(output),
        "delta_objects": hashes,
        "axioms": profiles,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (delta / "delta.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
