#!/usr/bin/env python3
"""Consume Raw112 on the official Raw39->Raw47 Canonical38 lineage."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
A50 = HERE.parent / "agent50-raw47-canonical41"
A17 = HERE.parent / "agent17-raw112-canonical58"
sys.path.insert(0, str(A50))
sys.path.insert(0, str(A17))

import consume_after_canonical40 as raw47
from assemble_canonical58_raw112_graft import verify_raw112_parent

c = raw47.c
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PREDECESSOR_ARTIFACT = "canonical38-raw39-then-raw47-delta"
PREDECESSOR_NS = "BB6.Agent9Canonical38Raw39ThenRaw47"
MEM_SOURCE = HERE / "Raw112Canonical38OfficialMembership.lean"
MEM_NS = "BB6.Agent9Raw112Canonical38OfficialMembership"
COND_SOURCE = HERE / "Raw112Canonical38OfficialConditional.lean"
COND_NS = "BB6.Agent9Raw112Canonical38OfficialConditional"
TARGET_NS = "BB6.Agent9Canonical37Raw39Raw47Raw112Official"
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"


def source_check(source: Path, linked: Path, evidence: Path, names):
    root, profile = c.u.compile_one(source, linked, evidence, names)
    if not set(names) <= set(profile):
        raise RuntimeError("missing axiom profiles: " + repr(set(names) - set(profile)))
    if not all(set(v) <= ALLOWED for v in profile.values()):
        raise RuntimeError("unapproved axiom profile: " + repr(profile))
    return root, profile


def restore_canonical40(work: Path):
    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = raw47.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    return linked, prior40, pin40


def restore_predecessor(work: Path, linked: Path, prior40: dict, pin40: dict,
                        run_id: int):
    run, item, pin = c.extra.artifact(run_id, PREDECESSOR_ARTIFACT)
    folder = work / "canonical38"
    folder.mkdir()
    dirs = c.a68.download(pin, folder)
    metadata = folder / "metadata" / str(item["id"])
    matches = list(metadata.rglob("delta.json"))
    assert len(matches) == 1, matches
    report = json.loads(matches[0].read_text())
    assert report["status"] == (
        "source-accepted Raw47 successor of accepted Raw39 Canonical39")
    assert report["source_revision"] == run["head_sha"]
    assert report["accepted_canonical39"]["run_id"] == 46129131784
    assert report["canonical40_delta"] == pin40
    assert report["canonical40_root_sha256"] == prior40["root_sha256"]
    assert report["accepted_canonical39"]["remaining_residual_count"] == 39
    assert report["previous_residual_count"] == 39
    assert report["remaining_residual_count"] == 38
    assert report["exact_at_champion_score"] == PREDECESSOR_NS + ".exact_at_champion_score"
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())

    objects = report["delta_objects"]
    observed = {}
    for d in dirs:
        for f in d.glob("*.olean"):
            if f.name in observed:
                assert c.a68.sha(observed[f.name]) == c.a68.sha(f), f.name
                continue
            observed[f.name] = f
    assert set(objects) == set(observed)
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


def integrated_source(folder: Path):
    source = folder / "Canonical37Raw39Raw47Raw112Official.lean"
    source.write_text("""import Raw112Canonical38OfficialConditional
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent9Canonical37Raw39Raw47Raw112Official

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p112 : PartialMachine :=
  BB6.Agent9Raw112Canonical38OfficialConditional.p112
noncomputable abbrev roster37 :=
  BB6.Agent9Raw112Canonical38OfficialConditional.roster37

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

theorem count37 : roster37.length = 37 :=
  BB6.Agent9Raw112Canonical38OfficialConditional.count37

theorem raw112_removed :
    (roster37.filter (fun e => sameTable e.2 p112)).length = 0 :=
  BB6.Agent9Raw112Canonical38OfficialConditional.removed_parent_absent

theorem sound37 :
    ∀ m, compatible root m →
      WeightedBound (proposedTM63Moves + 7) m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m :=
  BB6.Agent9Raw112Canonical38OfficialConditional.conditional_sound p112_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent9Raw112Canonical38OfficialConditional.conditional_exact_at_champion
    p112_cover hLeaves

#print axioms p112_source_eq
#print axioms p112_cover
#print axioms count37
#print axioms raw112_removed
#print axioms sound37
#print axioms exact_at_champion_score

end BB6.Agent9Canonical37Raw39Raw47Raw112Official
""")
    return source


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", required=True, type=Path)
    ap.add_argument("--canonical38-run-id", required=True, type=int)
    ap.add_argument("--raw112-run-id", type=int)
    ap.add_argument("--conditional-only", action="store_true")
    args = ap.parse_args()
    if not args.conditional_only and args.raw112_run_id is None:
        raise SystemExit("--raw112-run-id required unless --conditional-only")

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / (
        "canonical37-raw112-official-conditional-delta"
        if args.conditional_only else "canonical37-raw112-official-delta")
    evidence = delta / "evidence"
    objects = delta / "objects"
    generated = delta / "generated"
    for d in (evidence, objects, generated):
        d.mkdir(parents=True, exist_ok=True)

    linked, prior40, pin40 = restore_canonical40(work)
    prior38, pin38 = restore_predecessor(
        work, linked, prior40, pin40, args.canonical38_run_id)

    roots = []
    profiles = {}
    mem_names = [MEM_NS + ".parent_count38", MEM_NS + ".parent_root"]
    mem_root, mem_ax = source_check(MEM_SOURCE, linked, evidence, mem_names)
    roots.append(mem_root)
    profiles.update(mem_ax)

    cond_names = [
        COND_NS + ".parent_count38",
        COND_NS + ".count37",
        COND_NS + ".removed_parent_absent",
        COND_NS + ".conditional_sound",
        COND_NS + ".conditional_exact_at_champion",
    ]
    cond_root, cond_ax = source_check(COND_SOURCE, linked, evidence, cond_names)
    roots.append(cond_root)
    profiles.update(cond_ax)

    raw112_meta = None
    raw112_summary = None
    raw112_audit = None
    if not args.conditional_only:
        parent_work = work / "raw112"
        parent_work.mkdir()
        raw112_meta, raw112_dirs, raw112_summary = verify_raw112_parent(
            parent_work, args.raw112_run_id)
        copied = []
        raw112_audit = {}
        c.selected.add_family(
            {"root": "Raw112ClosedCover"},
            raw112_dirs, linked, copied, raw112_audit)
        assert (linked / "Raw112ClosedCover.olean").is_file()
        roots.extend(copied)

        source = integrated_source(generated)
        final_names = [
            TARGET_NS + ".p112_source_eq",
            TARGET_NS + ".p112_cover",
            TARGET_NS + ".count37",
            TARGET_NS + ".raw112_removed",
            TARGET_NS + ".sound37",
            TARGET_NS + ".exact_at_champion_score",
        ]
        final_root, final_ax = source_check(
            source, linked, evidence, final_names)
        roots.append(final_root)
        profiles.update(final_ax)
        root = final_root
        status = (
            "source-accepted Raw112 successor of official Raw39-then-Raw47 Canonical38")
        exact = TARGET_NS + ".exact_at_champion_score"
    else:
        root = cond_root
        status = (
            "source-accepted conditional Raw112 successor of official Canonical38")
        exact = COND_NS + ".conditional_exact_at_champion"

    hashes = {}
    for src in roots:
        dst = objects / src.name
        digest = c.a68.sha(src)
        if dst.exists():
            assert c.a68.sha(dst) == digest, src.name
        else:
            shutil.copy2(src, dst)
        hashes[dst.name] = digest

    report = {
        "status": status,
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "previous_delta": pin38,
        "previous_root_sha256": prior38["root_sha256"],
        "previous_residual_count": 38,
        "remaining_residual_count": 37,
        "raw112_parent_table": RAW112_TABLE,
        "raw112_parent_theorem": RAW112_THEOREM,
        "cover_premise": None if not args.conditional_only else (
            "Cover (WeightedBound (proposedTM63Moves + 7)) p112"),
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": (
            None if raw112_meta is None else raw112_meta["artifact_name"]),
        "raw112_artifact_id": (
            None if raw112_meta is None else raw112_meta["artifact_id"]),
        "raw112_artifact_sha256": (
            None if raw112_meta is None else raw112_meta["artifact_digest"]),
        "raw112_retry_summary": raw112_summary,
        "raw112_link_audit": raw112_audit,
        "root": root.name,
        "root_sha256": hashes[root.name],
        "delta_objects": hashes,
        "axioms": profiles,
        "exact_at_champion_score": exact,
    }
    (delta / "delta.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: official Canonical38 Raw112 "
        + ("conditional 38 -> 37 cut" if args.conditional_only
           else "parent consumed; exactly 37 Covers remain"),
        flush=True)


if __name__ == "__main__":
    main()
