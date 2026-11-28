#!/usr/bin/env python3
"""Build the official Raw39->Raw47 Canonical38 successor using authenticated transport objects.

The accepted public frontier is Raw39Canonical39Successor (run 46129131784).
For transport efficiency this consumer reuses the already authenticated
Raw39/Raw47 proof objects emitted by the direct common-ancestor join, but it
source-elaborates the *serial* theorem over the accepted Raw39 Canonical39
roster and therefore establishes the official 39 -> 38 lineage independently
of the direct roster theorem.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
A11 = HERE.parent / "agent11-raw39"
A3 = HERE.parent / "agent3-canonical38-raw47"
A50 = HERE.parent / "agent50-raw47-canonical41"
sys.path.insert(0, str(A50))

import consume_after_canonical40 as raw47

c = raw47.c
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ACCEPTED39_RUN = 46129131784
ACCEPTED39_ARTIFACT = 15258350500
ACCEPTED39_DIGEST = "aa5706bd0657478d66b1707bdd16e73101047e6f26206157c91f8312035d4557"
ACCEPTED39_HEAD = "6d5196868ae0d95c217b54a308550b9bfd5572ba"
ACCEPTED39_SOURCE_BLOB = "f3e7cc6d3c67ba5c3c671637d63e9e5900cfd089"
DIRECT_ARTIFACT = "canonical38-raw39-raw47-direct-delta"
DIRECT_NS = "BB6.Agent3Canonical38Raw39Raw47Direct"
COND_NS = "BB6.Agent3Raw47Canonical39Conditional"
TARGET_NS = "BB6.Agent9Canonical38Raw39ThenRaw47"
RAW39_TARGETS = [
    "BB6.Agent11Raw39Canonical39Successor.count39",
    "BB6.Agent11Raw39Canonical39Successor.raw39_cover",
    "BB6.Agent11Raw39Canonical39Successor.sound_integrated",
    "BB6.Agent11Raw39Canonical39Successor.exact_at_champion_score",
]
COND_TARGETS = [
    COND_NS + ".parent_count39",
    COND_NS + ".count38",
    COND_NS + ".raw47_removed",
    COND_NS + ".conditional_sound",
    COND_NS + ".conditional_exact_at_champion",
]
FINAL_TARGETS = [
    TARGET_NS + ".raw47_literal_agreement",
    TARGET_NS + ".raw47_cover",
    TARGET_NS + ".sound38",
    TARGET_NS + ".sound38_at",
    TARGET_NS + ".exact_at_champion_score",
]


def source_check(source: Path, linked: Path, evidence: Path, names):
    root, profile = c.u.compile_one(source, linked, evidence, names)
    if not set(names) <= set(profile):
        raise RuntimeError("missing axiom profiles: " + repr(set(names) - set(profile)))
    if not all(set(v) <= ALLOWED for v in profile.values()):
        raise RuntimeError("unapproved axiom profile: " + repr(profile))
    return root, profile


def authenticate_accepted39(evidence: Path):
    run = c.a68.api_json(f"repos/FlareZ123/bb6/actions/runs/{ACCEPTED39_RUN}")
    assert run["conclusion"] == "success"
    assert run["head_sha"] == ACCEPTED39_HEAD
    arts = c.a68.api_json(f"repos/FlareZ123/bb6/actions/runs/{ACCEPTED39_RUN}/artifacts")
    matches = [x for x in arts["artifacts"]
               if x["id"] == ACCEPTED39_ARTIFACT and not x["expired"]]
    assert len(matches) == 1
    art = matches[0]
    assert art["name"] == "raw39-global-source-global-parent-chunked"
    assert art["digest"] == "sha256:" + ACCEPTED39_DIGEST
    receipt = {
        "run_id": ACCEPTED39_RUN,
        "head_sha": ACCEPTED39_HEAD,
        "artifact_id": ACCEPTED39_ARTIFACT,
        "artifact_sha256": ACCEPTED39_DIGEST,
        "theorem": "BB6.Agent11Raw39Canonical39Successor.exact_at_champion_score",
        "remaining_residual_count": 39,
    }
    (evidence / "accepted-canonical39.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return receipt


def restore_transport(work: Path, linked: Path, prior40: dict, pin40: dict,
                      run_id: int):
    run, item, pin = c.extra.artifact(run_id, DIRECT_ARTIFACT)
    folder = work / "direct-transport"
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
    assert report["onele_run"] == 46114235329
    assert report["raw47_run_id"] == 46068688341
    assert report["exact_at_champion_score"] == DIRECT_NS + ".exact_at_champion_score"
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())

    objects = report["delta_objects"]
    observed = {}
    for directory in dirs:
        for file in directory.glob("*.olean"):
            if file.name in observed:
                assert c.a68.sha(observed[file.name]) == c.a68.sha(file), file.name
                continue
            observed[file.name] = file
    assert set(objects) == set(observed)
    carried = []
    for name, digest in objects.items():
        assert name == Path(name).name
        assert c.a68.sha(observed[name]) == digest, name
        dest = linked / name
        if dest.exists():
            assert c.a68.sha(dest) == digest, name
        else:
            shutil.copy2(observed[name], dest)
            carried.append(dest)
    assert (linked / "Raw39Canonical40Bridge.olean").is_file()
    assert (linked / "Raw47KernelBridge.olean").is_file()
    return report, {
        "run_id": run_id,
        "artifact_id": item["id"],
        "artifact_sha256": pin[2],
        "root_sha256": report["root_sha256"],
    }, carried


def final_source(folder: Path):
    source = folder / "Canonical38Raw39ThenRaw47.lean"
    source.write_text("""import Raw47Canonical39Conditional
import Raw47KernelBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent9Canonical38Raw39ThenRaw47

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p47 : PartialMachine :=
  BB6.Agent3Raw47Canonical39Conditional.p47
noncomputable abbrev roster38 :=
  BB6.Agent3Raw47Canonical39Conditional.roster38

theorem raw47_literal_agreement :
    p47 = BB6.Agent50Raw47Bridge.parent :=
  sameTable_sound (by decide)

theorem raw47_cover :
    Cover (WeightedBound 6766859) p47 := by
  rw [raw47_literal_agreement]
  exact BB6.Agent50Raw47Bridge.cover_at 6766859 (by decide)

theorem sound38 :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m :=
  BB6.Agent3Raw47Canonical39Conditional.conditional_sound raw47_cover

theorem sound38_at (B : Nat) (hFloor : 6766859 ≤ B) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound38 m hm with hsmall | hrest
  · exact Or.inl (fun k d hk hd =>
      Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  BB6.Agent3Raw47Canonical39Conditional.conditional_exact_at_champion
    raw47_cover hLeaves

#print axioms raw47_literal_agreement
#print axioms raw47_cover
#print axioms sound38
#print axioms sound38_at
#print axioms exact_at_champion_score

end BB6.Agent9Canonical38Raw39ThenRaw47
""")
    return source


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--direct38-run-id", type=int, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical38-raw39-then-raw47-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    generated = delta / "generated"
    for d in (evidence, objects, generated):
        d.mkdir(parents=True, exist_ok=True)

    accepted39 = authenticate_accepted39(evidence)
    source_blob = subprocess.check_output(
        ["git", "hash-object", str(A11 / "Raw39Canonical39Successor.lean")],
        cwd=REPO, text=True).strip()
    assert source_blob == ACCEPTED39_SOURCE_BLOB
    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = raw47.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40

    transport_report, transport_pin, carried = restore_transport(
        work, linked, prior40, pin40, args.direct38_run_id)
    roots = list(carried)
    profiles = {}
    root39, ax39 = source_check(
        A11 / "Raw39Canonical39Successor.lean",
        linked, evidence, RAW39_TARGETS)
    roots.append(root39)
    profiles.update(ax39)
    root_cond, ax_cond = source_check(
        A3 / "Raw47Canonical39Conditional.lean",
        linked, evidence, COND_TARGETS)
    roots.append(root_cond)
    profiles.update(ax_cond)
    source = final_source(generated)
    root_final, ax_final = source_check(source, linked, evidence, FINAL_TARGETS)
    roots.append(root_final)
    profiles.update(ax_final)

    hashes = {}
    for src in roots:
        dst = objects / src.name
        shutil.copy2(src, dst)
        hashes[dst.name] = c.a68.sha(dst)

    report = {
        "status": "source-accepted Raw47 successor of accepted Raw39 Canonical39",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "accepted_canonical39": accepted39,
        "canonical40_delta": pin40,
        "canonical40_root_sha256": prior40["root_sha256"],
        "transport_carrier": transport_pin,
        "transport_carrier_status": transport_report["status"],
        "previous_residual_count": 39,
        "remaining_residual_count": 38,
        "root": root_final.name,
        "root_sha256": hashes[root_final.name],
        "delta_objects": hashes,
        "axioms": profiles,
        "exact_at_champion_score": TARGET_NS + ".exact_at_champion_score",
    }
    (delta / "delta.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw39 Canonical39 -> Raw47 -> Canonical38 "
        "source-checked; exactly 38 Covers remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
