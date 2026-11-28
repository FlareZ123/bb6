#!/usr/bin/env python3
"""Source-check Raw112 as the next accepted parent after direct Canonical38."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
REPO = HERE.parents[1]
A50 = SIBLINGS / "agent50-raw47-canonical41"
A17 = SIBLINGS / "agent17-raw112-canonical58"
sys.path.insert(0, str(A50))
sys.path.insert(0, str(A17))

import consume_after_canonical40 as raw47
import assemble_canonical58_raw112_graft as raw112

c = raw47.c
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DIRECT_ARTIFACT = "canonical38-raw39-raw47-direct-delta"
DIRECT_STATUS = "source-accepted direct Raw39 plus Raw47 successor of Canonical40"
NS = "BB6.Agent17Canonical37Raw112AfterDirect38"
TARGETS = [
    NS + "." + name
    for name in (
        "p112_count38",
        "p112_cover_floor",
        "raw39_cover_floor",
        "raw47_cover_floor",
        "predecessor_sound",
        "count37",
        "raw112_removed",
        "sound_integrated",
        "sound_at",
        "exact_at_champion_score",
    )
]


def restore_canonical40(work: Path):
    work.mkdir(parents=True, exist_ok=False)
    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = raw47.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40
    return linked, prior40, pin40


def restore_direct38(work: Path, linked: Path, prior40: dict, pin40: dict,
                     run_id: int):
    run, item, pin = c.extra.artifact(run_id, DIRECT_ARTIFACT)
    assert run["conclusion"] == "success", run.get("conclusion")
    folder = work / "direct38-artifact"
    folder.mkdir()
    dirs = c.a68.download(pin, folder)

    metadata = folder / "metadata" / str(item["id"])
    reports = list(metadata.rglob("delta.json"))
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["status"] == DIRECT_STATUS
    assert report["source_revision"] == run["head_sha"]
    assert report["previous_delta"] == pin40
    assert report["previous_root_sha256"] == prior40["root_sha256"]
    assert report["previous_residual_count"] == 40
    assert report["remaining_residual_count"] == 38
    assert report["onele_run"] == 46114235329
    assert report["raw47_run_id"] == 46068688341
    assert report["exact_at_champion_score"] == (
        "BB6.Agent3Canonical38Raw39Raw47Direct.exact_at_champion_score"
    )
    assert all(set(v) <= ALLOWED for v in report["axioms"].values())

    observed = {}
    for directory in dirs:
        for file in directory.glob("*.olean"):
            prior = observed.get(file.name)
            if prior is not None:
                assert c.a68.sha(prior) == c.a68.sha(file), file.name
            else:
                observed[file.name] = file

    objects = report["delta_objects"]
    assert set(objects) == set(observed), (
        sorted(set(objects) - set(observed)),
        sorted(set(observed) - set(objects)),
    )
    for name, digest in objects.items():
        assert c.a68.sha(observed[name]) == digest, name
        dest = linked / name
        if dest.exists():
            assert c.a68.sha(dest) == digest, name
        else:
            shutil.copy2(observed[name], dest)

    root = linked / report["root"]
    assert root.is_file()
    assert c.a68.sha(root) == report["root_sha256"]
    receipt = {
        "run_id": run_id,
        "head_sha": run["head_sha"],
        "artifact_id": item["id"],
        "artifact_name": item["name"],
        "artifact_sha256": pin[2],
        "root": report["root"],
        "root_sha256": report["root_sha256"],
        "remaining_residual_count": 38,
    }
    shutil.rmtree(folder)
    return report, receipt


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--direct38-run-id", type=int, required=True)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    linked, prior40, pin40 = restore_canonical40(work / "canonical")
    direct, direct_receipt = restore_direct38(
        work, linked, prior40, pin40, args.direct38_run_id)

    raw112_work = work / "raw112-parent"
    raw112_work.mkdir()
    meta, dirs, summary = raw112.verify_raw112_parent(
        raw112_work, args.raw112_run_id)
    copied = []
    link_audit = {}
    raw112.selected.add_family(
        {"root": "Raw112ClosedCover"}, dirs, linked, copied, link_audit)
    assert (linked / "Raw112ClosedCover.olean").is_file()

    source = HERE / "Canonical37Raw112AfterDirect38.lean"
    root, profile = c.u.compile_one(source, linked, evidence, TARGETS)
    assert set(TARGETS) <= set(profile), (
        set(TARGETS) - set(profile))
    assert all(set(ax) <= ALLOWED for ax in profile.values()), profile

    report = {
        "status": (
            "source-checked Raw112 successor of accepted direct Canonical38"
        ),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "direct38": direct_receipt,
        "direct38_predecessor": direct["previous_delta"],
        "previous_residual_count": 38,
        "remaining_residual_count": 37,
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": meta["artifact_name"],
        "raw112_artifact_id": meta["artifact_id"],
        "raw112_artifact_sha256": meta["artifact_digest"],
        "raw112_proof_source_revision": meta["source_revision"],
        "raw112_assembly_revision": meta.get("assembly_revision"),
        "raw112_parent_table": raw112.RAW112_TABLE,
        "raw112_parent_theorem": raw112.RAW112_THEOREM,
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": summary,
        "raw112_link_audit": link_audit,
        "axioms": profile,
        "root": root.name,
        "root_sha256": c.a68.sha(root),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
    }
    (evidence / "canonical37-raw112-after-direct38.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted direct Canonical38 -> Raw112 -> Canonical37; "
        "exactly 37 Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
