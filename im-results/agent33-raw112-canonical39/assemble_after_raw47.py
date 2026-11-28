#!/usr/bin/env python3
"""Consume an accepted Raw112 parent on the accepted Raw47 Canonical39 lineage."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
sys.path.insert(0, str(SIBLINGS / "agent50-raw47-canonical41"))
sys.path.insert(0, str(SIBLINGS / "agent45-canonical38-raw39"))
sys.path.insert(0, str(SIBLINGS / "agent17-raw112-canonical58"))

import consume as c
from consume_after_canonical40 import restore_canonical40
from consume_after_raw47 import restore_canonical39
from assemble_canonical58_raw112_graft import verify_raw112_parent

TARGET_NS = "BB6.Agent33Canonical38Raw47Raw112"
PREV_NS = "BB6.Agent50Canonical39Raw47"
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def generate_source(work: Path):
    source = work / "Canonical38Raw47Raw112.lean"
    source.write_text("""import Canonical39Raw47
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent33Canonical38Raw47Raw112

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster := BB6.Agent50Canonical39Raw47.roster39
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent
abbrev removedParents : List PartialMachine := [p112]

theorem p112_count39 :
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

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_cover

noncomputable def roster38 := removeParents removedParents baseRoster

theorem count38 : roster38.length = 38 := by decide

theorem raw112_removed :
    (roster38.filter (fun e => sameTable e.2 p112)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent50Canonical39Raw47.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster38, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count39
#print axioms p112_cover
#print axioms count38
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent33Canonical38Raw47Raw112
""")
    names = [
        TARGET_NS + ".p112_count39",
        TARGET_NS + ".p112_cover",
        TARGET_NS + ".count38",
        TARGET_NS + ".raw112_removed",
        TARGET_NS + ".sound_integrated",
        TARGET_NS + ".exact_at_target",
        TARGET_NS + ".exact_at_champion_score",
    ]
    return source, names


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--canonical39-run-id", type=int, required=True)
    ap.add_argument("--raw112-run-id", type=int, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical38-raw47-raw112-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    generated = delta / "generated"
    for directory in (evidence, objects, generated):
        directory.mkdir(parents=True, exist_ok=True)

    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    prior39, pin39 = restore_canonical39(
        work, linked, prior40, pin40, args.canonical39_run_id)
    assert prior39["remaining_residual_count"] == 39
    assert prior39["exact_at_champion_score"] == PREV_NS + ".exact_at_champion_score"

    raw112_work = work / "raw112"
    raw112_work.mkdir()
    raw112_meta, raw112_dirs, raw112_summary = verify_raw112_parent(
        raw112_work, args.raw112_run_id)

    copied = []
    audit = {}
    c.selected.add_family(
        {"root": "Raw112ClosedCover"}, raw112_dirs, linked, copied, audit)
    assert (linked / "Raw112ClosedCover.olean").is_file()

    source, names = generate_source(generated)
    env = dict(os.environ, LEAN_PATH=str(linked))
    output = linked / (source.stem + ".olean")
    log = c.a68.compile_module(source, output, env, work / "canonical38.log")
    profiles = c.a68.gate(log, names)
    assert all(set(v) <= ALLOWED for v in profiles.values())
    copied.append(output)

    hashes = {}
    for src in copied:
        dst = objects / src.name
        if dst.exists():
            assert c.a68.sha(dst) == c.a68.sha(src), src.name
            continue
        shutil.copy2(src, dst)
        hashes[dst.name] = c.a68.sha(dst)

    report = {
        "status": "source-accepted Raw112 successor of Canonical39 Raw47",
        "previous_delta": pin39,
        "previous_root_sha256": prior39["root_sha256"],
        "previous_residual_count": 39,
        "remaining_residual_count": 38,
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
        "root_sha256": c.a68.sha(output),
        "delta_objects": hashes,
        "axioms": profiles,
        "exact_at_champion_score": TARGET_NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip(),
    }
    (delta / "delta.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
