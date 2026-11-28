#!/usr/bin/env python3
"""Build the Raw39 conditional quotient directly on the accepted Raw47 Canonical39 successor.

This consumer deliberately does not claim Raw39 is solved. It proves, against
the actual accepted 39-roster, that Raw39 occurs exactly once and that supplying
its Cover leaves exactly 38 quotient representatives.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
sys.path.insert(0, str(SIBLINGS / "agent50-raw47-canonical41"))

import consume as c
from consume_after_canonical40 import restore_canonical40

TARGET_NS = "BB6.Agent45Canonical38Raw47Raw39Conditional"
PREV_NS = "BB6.Agent50Canonical39Raw47"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def restore_canonical39(work, linked, canonical40, predecessor_pin, run_id):
    run, item, pin = c.extra.artifact(run_id, "canonical39-raw47-thin-delta")
    folder = work / "canonical39-raw47"
    folder.mkdir()
    dirs = c.a68.download(pin, folder)
    metadata = folder / "metadata" / str(item["id"])
    matches = list(metadata.rglob("delta.json"))
    assert len(matches) == 1, matches
    report = json.loads(matches[0].read_text())
    assert report["status"] == "source-accepted Raw47 successor of Canonical40"
    assert report["source_revision"] == run["head_sha"]
    assert report["previous_delta"] == predecessor_pin
    assert report["previous_root_sha256"] == canonical40["root_sha256"]
    assert report["previous_residual_count"] == 40
    assert report["remaining_residual_count"] == 39
    assert report["transport"] == "staged"
    assert report["exact_at_champion_score"] == PREV_NS + ".exact_at_champion_score"
    assert report["exact_at_champion_score"] in report["axioms"]
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())

    objects = report["delta_objects"]
    observed = {}
    for directory in dirs:
        for file in directory.glob("*.olean"):
            if file.name in observed:
                assert c.a68.sha(observed[file.name]) == c.a68.sha(file), file.name
                continue
            observed[file.name] = file
    assert set(objects) == set(observed), (set(objects) - set(observed), set(observed) - set(objects))
    assert objects[report["root"]] == report["root_sha256"]
    for name, digest in objects.items():
        assert name == Path(name).name
        assert c.a68.sha(observed[name]) == digest, name
        dest = linked / name
        assert not dest.exists(), name
        shutil.copy2(observed[name], dest)
    return report, {
        "run_id": run_id,
        "artifact_id": item["id"],
        "artifact_sha256": pin[2],
        "root_sha256": report["root_sha256"],
    }


def generate_source(work):
    source = work / "Canonical38Raw47Raw39Conditional.lean"
    source.write_text("""import Canonical39Raw47

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent45Canonical38Raw47Raw39Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

def p39 : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,0⟩)
  | _,_ => none

noncomputable abbrev baseRoster := BB6.Agent50Canonical39Raw47.roster39
abbrev removedParents : List PartialMachine := [p39]

theorem parent_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p39)).length = 1 := by decide

theorem parent_root :
    p39 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p39 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover (B : Nat) (hp : Cover (WeightedBound B) p39) :
    ∀ p ∈ removedParents, Cover (WeightedBound B) p := by
  intro p hmem
  have he : p = p39 := by simpa [removedParents] using hmem
  subst p
  exact hp

noncomputable def roster38 := removeParents removedParents baseRoster

theorem count38 : roster38.length = 38 := by decide

theorem removed_parent_absent :
    (roster38.filter (fun e => sameTable e.2 p39)).length = 0 := by decide

theorem sound39_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ baseRoster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent50Canonical39Raw47.sound_integrated m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem conditional_sound_at (B : Nat) (hFloor : 6766859 ≤ B)
    (hp : Cover (WeightedBound B) p39) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m :=
  removeParents_sound (sound39_at B hFloor) parents_root (parents_cover B hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound (proposedTM63Moves + 7)) p39)
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega) (Nat.le_refl _)
    (conditional_sound_at (proposedTM63Moves + 7)
      BB6.Agent38ChampionThreshold.champion_score_ge_6766859 hp)
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count39
#print axioms count38
#print axioms removed_parent_absent
#print axioms sound39_at
#print axioms conditional_sound_at
#print axioms conditional_exact_at_champion

end BB6.Agent45Canonical38Raw47Raw39Conditional
""")
    names = [
        TARGET_NS + ".parent_count39",
        TARGET_NS + ".count38",
        TARGET_NS + ".removed_parent_absent",
        TARGET_NS + ".sound39_at",
        TARGET_NS + ".conditional_sound_at",
        TARGET_NS + ".conditional_exact_at_champion",
    ]
    return source, names


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--canonical39-run-id", type=int, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical38-raw47-raw39-conditional-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

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

    source, names = generate_source(work)
    root, profiles = c.u.compile_one(source, linked, evidence, names)
    assert all(set(v) <= ALLOWED for v in profiles.values())

    dst = objects / root.name
    shutil.copy2(root, dst)
    hashes = {dst.name: c.a68.sha(dst)}
    report = {
        "status": "source-accepted conditional Raw39 successor of Canonical39 Raw47",
        "previous_delta": pin39,
        "previous_root_sha256": prior39["root_sha256"],
        "previous_residual_count": 39,
        "remaining_residual_count": 38,
        "conditional_parent": "Raw39",
        "axioms": profiles,
        "root": root.name,
        "root_sha256": hashes[root.name],
        "delta_objects": hashes,
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip(),
        "conditional_exact_at_champion":
            TARGET_NS + ".conditional_exact_at_champion",
    }
    c.save_json(delta / "delta.json", report)
    print("PASS: actual Raw47 Canonical39 has unique Raw39; conditional roster has 38 Covers",
          flush=True)


if __name__ == "__main__":
    main()
