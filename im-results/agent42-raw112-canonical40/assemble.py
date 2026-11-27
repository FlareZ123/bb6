#!/usr/bin/env python3
"""Consume an accepted Raw112 parent Cover directly on the accepted Canonical41 boundary."""
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
sys.path.insert(0, str(REPO_ROOT / "im-results" / "agent17-raw112-canonical58"))
sys.path.insert(0, str(REPO_ROOT / "im-results" / "agent31-shared-core"))

import extra_ready_union as extra
import resume_ready_union as resume
import assemble_canonical68 as a68
import assemble_canonical_selected as selected
from assemble_canonical58_raw112_graft import verify_raw112_parent

REPO = "FlareZ123/bb6"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"
NS = "BB6.Agent42Canonical40Raw112"


def restore_extra(work: Path, linked: Path, ready_report: dict, ready_pin: dict, run_id: int):
    work.mkdir(parents=True, exist_ok=True)
    run, item, pin = extra.artifact(run_id, "canonical-extra-ready-thin-delta")
    dirs = a68.download(pin, work)
    metadata = work / "metadata" / str(item["id"])
    reports = list(metadata.rglob("delta.json"))
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["status"] == "source-accepted additional ready-parent subset"
    assert report["source_revision"] == run["head_sha"]
    assert report["ready_predecessor"] == ready_pin
    assert report["previous_root_sha256"] == ready_report["root_sha256"]
    assert report["previous_residual_count"] == ready_report["remaining_residual_count"]
    assert report["remaining_residual_count"] == 41
    assert report["exact_at_champion_score"].endswith(".exact_at_champion_score")
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())
    objects = report["delta_objects"]
    observed = {}
    for d in dirs:
        for f in d.glob("*.olean"):
            assert f.name not in observed, f.name
            observed[f.name] = f
    assert set(observed) == set(objects), (sorted(observed), sorted(objects))
    assert objects[report["root"]] == report["root_sha256"]
    for name, digest in objects.items():
        assert a68.sha(observed[name]) == digest, name
        dest = linked / name
        assert not dest.exists(), name
        shutil.copy2(observed[name], dest)
    ns = report["exact_at_champion_score"].rsplit(".", 1)[0]
    return report, ns, {
        "run_id": run_id,
        "artifact_id": item["id"],
        "artifact_sha256": pin[2],
        "root_sha256": report["root_sha256"],
    }


def generate(prior: dict, prior_ns: str, folder: Path):
    module = "Canonical40Raw112AfterCanonical41"
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

noncomputable abbrev baseRoster := {prior_ns}.roster41
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent

theorem p112_count41 :
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

noncomputable def roster40 := removeParents parents baseRoster

theorem count40 : roster40.length = 40 := by decide

theorem raw112_removed :
    (roster40.filter (fun e => sameTable e.2 p112)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster40, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := parents)
    (roster := baseRoster)
    {prior_ns}.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster40, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster40,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count41
#print axioms p112_cover
#print axioms parents_pairwise_distinct
#print axioms count40
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
    ap.add_argument("--ready-run-id", type=int, default=46031670976)
    ap.add_argument("--canonical41-run-id", type=int, default=46037391095)
    ap.add_argument("--raw112-run-id", type=int, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    generated = delta / "generated"
    for d in (evidence, objects, generated):
        d.mkdir(parents=True, exist_ok=True)

    linked, _, _, base_report = extra.base.verify_base(work, extra.base.BASE_RUN)
    sharp = resume.restore_sharp(work, linked, base_report)
    ready, ready_ns, ready_pin = extra.restore_ready(work, linked, sharp, args.ready_run_id)
    prior, prior_ns, prior_pin = restore_extra(
        work / "canonical41", linked, ready, ready_pin, args.canonical41_run_id
    )
    assert prior_ns != ready_ns

    raw112_work = work / "raw112"
    raw112_work.mkdir()
    raw112_meta, raw112_dirs, raw112_summary = verify_raw112_parent(raw112_work, args.raw112_run_id)

    before = set(linked.glob("*.olean"))
    audit = {}
    copied = []
    selected.add_family({"root": "Raw112ClosedCover"}, raw112_dirs, linked, copied, audit)
    assert (linked / "Raw112ClosedCover.olean").is_file()

    source = generate(prior, prior_ns, generated)
    env = dict(os.environ, LEAN_PATH=str(linked))
    output = linked / (source.stem + ".olean")
    log = a68.compile_module(source, output, env, work / "canonical40.log")
    names = [
        NS + ".p112_count41",
        NS + ".p112_cover",
        NS + ".parents_pairwise_distinct",
        NS + ".count40",
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
        "status": "source-accepted Canonical41-to-40 Raw112 delta",
        "canonical41_predecessor": prior_pin,
        "previous_root_sha256": prior["root_sha256"],
        "previous_residual_count": 41,
        "remaining_residual_count": 40,
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
    (delta / "delta.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
