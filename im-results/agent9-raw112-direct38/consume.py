#!/usr/bin/env python3
"""Consume an accepted Raw112 whole-parent Cover on direct Canonical38.

The predecessor is the source-accepted direct Canonical40 -> Canonical38
artifact that consumes Raw39 and Raw47 together.  This consumer authenticates
that exact delta, imports the independently source-accepted Raw112 parent
Cover, removes Raw112 by literal table identity, and source-checks the
Canonical37 exact-at-champion interface.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
A50 = SIBLINGS / "agent50-raw47-canonical41"
A17 = SIBLINGS / "agent17-raw112-canonical58"
sys.path.insert(0, str(A50))
sys.path.insert(0, str(A17))

import consume_after_canonical40 as raw47
from assemble_canonical58_raw112_graft import verify_raw112_parent

c = raw47.c

DIRECT_ARTIFACT = "canonical38-raw39-raw47-direct-delta"
DIRECT_NS = "BB6.Agent3Canonical38Raw39Raw47Direct"
TARGET_NS = "BB6.Agent9Canonical37Raw39Raw47Raw112Direct"
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"
MEMBERSHIP_SOURCE = HERE / "Raw112Canonical38DirectMembership.lean"
MEMBERSHIP_NS = "BB6.Agent9Raw112Canonical38DirectMembership"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def restore_direct38(work: Path, linked: Path, prior40: dict, pin40: dict,
                     run_id: int):
    run, item, pin = c.extra.artifact(run_id, DIRECT_ARTIFACT)
    folder = work / "direct38"
    folder.mkdir()
    dirs = c.a68.download(pin, folder)
    metadata = folder / "metadata" / str(item["id"])
    matches = list(metadata.rglob("delta.json"))
    assert len(matches) == 1, matches
    report = json.loads(matches[0].read_text())

    assert report["status"] == (
        "source-accepted direct Raw39 plus Raw47 successor of Canonical40")
    assert report["source_revision"] == run["head_sha"]
    assert report["previous_delta"] == pin40
    assert report["previous_root_sha256"] == prior40["root_sha256"]
    assert report["previous_residual_count"] == 40
    assert report["remaining_residual_count"] == 38
    assert report["exact_at_champion_score"] == (
        DIRECT_NS + ".exact_at_champion_score")
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

    assert set(objects) == set(observed), (
        set(objects) - set(observed), set(observed) - set(objects))
    assert objects[report["root"]] == report["root_sha256"]
    for name, digest in objects.items():
        assert name == Path(name).name
        assert c.a68.sha(observed[name]) == digest, name
        dest = linked / name
        if dest.exists():
            assert c.a68.sha(dest) == digest, name
        else:
            shutil.copy2(observed[name], dest)

    return report, {
        "run_id": run_id,
        "artifact_id": item["id"],
        "artifact_sha256": pin[2],
        "root_sha256": report["root_sha256"],
    }


def generate_source(folder: Path):
    source = folder / "Canonical37Raw39Raw47Raw112Direct.lean"
    source.write_text("""import Raw112Canonical38DirectMembership
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent9Canonical37Raw39Raw47Raw112Direct

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent3Canonical38Raw39Raw47Direct.roster38
abbrev p112 : PartialMachine :=
  BB6.Agent9Raw112Canonical38DirectMembership.p112
abbrev removedParents : List PartialMachine := [p112]

theorem p112_count38 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 :=
  BB6.Agent9Raw112Canonical38DirectMembership.parent_count38

theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent9Raw112Canonical38DirectMembership.parent_root

theorem p112_source_eq : p112 = BB6.Agent47Raw112.parent :=
  sameTable_sound (by decide)

theorem p112_cover :
    Cover (WeightedBound (proposedTM63Moves + 7)) p112 := by
  rw [p112_source_eq]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by omega)

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_root

theorem parents_cover :
    ∀ p ∈ removedParents,
      Cover (WeightedBound (proposedTM63Moves + 7)) p := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_cover

noncomputable def roster37 := removeParents removedParents baseRoster

theorem count37 : roster37.length = 37 := by
  decide

theorem raw112_removed :
    (roster37.filter (fun e => sameTable e.2 p112)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound (proposedTM63Moves + 7) m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent3Canonical38Raw39Raw47Direct.sound38_at_champion
    parents_root parents_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster
    (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    sound_integrated
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count38
#print axioms p112_source_eq
#print axioms p112_cover
#print axioms count37
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms exact_at_champion_score

end BB6.Agent9Canonical37Raw39Raw47Raw112Direct
""")
    names = [
        TARGET_NS + ".p112_count38",
        TARGET_NS + ".p112_source_eq",
        TARGET_NS + ".p112_cover",
        TARGET_NS + ".count37",
        TARGET_NS + ".raw112_removed",
        TARGET_NS + ".sound_integrated",
        TARGET_NS + ".exact_at_champion_score",
    ]
    return source, names


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--direct38-run-id", type=int, required=True)
    ap.add_argument("--raw112-run-id", type=int)
    ap.add_argument("--membership-only", action="store_true")
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical37-direct38-raw112-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    generated = delta / "generated"
    for directory in (evidence, objects, generated):
        directory.mkdir(parents=True, exist_ok=True)

    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(
        work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = raw47.restore_canonical40(
        work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40

    prior38, pin38 = restore_direct38(
        work, linked, prior40, pin40, args.direct38_run_id)
    assert prior38["remaining_residual_count"] == 38

    membership_output = linked / (MEMBERSHIP_SOURCE.stem + ".olean")
    membership_log = c.a68.compile_module(
        MEMBERSHIP_SOURCE, membership_output,
        dict(os.environ, LEAN_PATH=str(linked)),
        work / "membership.log")
    membership_names = [
        MEMBERSHIP_NS + ".parent_count38",
        MEMBERSHIP_NS + ".parent_root",
    ]
    membership_profiles = c.a68.gate(membership_log, membership_names)
    assert all(set(v) <= ALLOWED for v in membership_profiles.values())

    if args.membership_only:
        report = {
            "status": "source-accepted Raw112 membership on direct Canonical38",
            "source_revision": subprocess.check_output(
                ["git", "rev-parse", "HEAD"],
                cwd=HERE.parents[1], text=True).strip(),
            "previous_delta": pin38,
            "previous_root_sha256": prior38["root_sha256"],
            "previous_residual_count": 38,
            "raw112_parent_table": RAW112_TABLE,
            "raw112_literal_count": 1,
            "direct38_run_id": args.direct38_run_id,
            "root": membership_output.name,
            "root_sha256": c.a68.sha(membership_output),
            "axioms": membership_profiles,
        }
        out = work / "membership"
        out.mkdir()
        shutil.copy2(membership_output, out / membership_output.name)
        (out / "membership.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\\n")
        print(
            "PASS: Raw112 occurs exactly once in accepted direct Canonical38",
            flush=True,
        )
        return

    if args.raw112_run_id is None:
        raise SystemExit("--raw112-run-id is required unless --membership-only")

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
    log = c.a68.compile_module(source, output, env, work / "canonical37.log")
    profiles = c.a68.gate(log, names)
    assert all(set(v) <= ALLOWED for v in profiles.values())

    copied.append(output)
    hashes = {}
    for src in copied:
        dst = objects / src.name
        digest = c.a68.sha(src)
        if dst.exists():
            assert c.a68.sha(dst) == digest, src.name
        else:
            shutil.copy2(src, dst)
        hashes[dst.name] = digest

    report = {
        "status": (
            "source-accepted Raw112 successor of direct Raw39+Raw47 Canonical38"),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=HERE.parents[1], text=True).strip(),
        "previous_delta": pin38,
        "previous_root_sha256": prior38["root_sha256"],
        "previous_residual_count": 38,
        "remaining_residual_count": 37,
        "direct38_run_id": args.direct38_run_id,
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
        "exact_at_champion_score":
            TARGET_NS + ".exact_at_champion_score",
    }
    (delta / "delta.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw112 consumed from direct Canonical38; "
        "exactly 37 source-certified quotient obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
