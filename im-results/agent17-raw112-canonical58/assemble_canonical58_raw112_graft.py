#!/usr/bin/env python3
"""Compose the accepted Raw113 Canonical58 base with the accepted Raw112 parent Cover."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))

import assemble_canonical68 as a68
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
NS = "BB6.Agent17Canonical57Raw112Graft"
MEM = "BB6.Agent17Canonical59Raw112Membership"
RAW113_ARTIFACT = "canonical58-raw113-graft-integrated"
RAW112_ARTIFACT = "raw112-closed-parent-cover"
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"


def verify_raw113_base(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    candidates = [x for x in artifacts if x["name"] == RAW113_ARTIFACT]
    assert len(candidates) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = candidates[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")
    pin = (item["id"], run_id, digest)
    dirs = a68.download(pin, work)
    roots = [p for p in dirs if (p / "Canonical58Raw113Graft.olean").is_file()]
    assert len(roots) == 1, [str(p) for p in roots]

    metadata = work / "metadata" / str(item["id"])
    reports = list(metadata.rglob("canonical58-raw113-graft.json"))
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["base_run_id"] == 45880290680
    assert report["base_residual_count"] == 59
    assert report["remaining_residual_count"] == 58
    assert report["raw59_retained"]
    assert report["source_revision"] == run["head_sha"]
    assert report["olean_sha256"] == a68.sha(roots[0] / "Canonical58Raw113Graft.olean")
    profiles = [report["membership_axioms"], report["axioms"]]
    assert "sorryAx" not in str(profiles)
    assert "native_decide" not in str(profiles)
    return dirs, pin, item, report


def verify_raw112_parent(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    candidates = [x for x in artifacts if x["name"] == RAW112_ARTIFACT]
    assert len(candidates) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = candidates[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")
    pin = (item["id"], run_id, digest)
    dirs = a68.download(pin, work)
    assert any((d / "Raw112ClosedCover.olean").is_file() for d in dirs)

    metadata = work / "metadata" / str(item["id"])
    summaries = list(metadata.rglob("retry-summary.json"))
    manifests = list(metadata.rglob("manifest.json"))
    assert len(summaries) == 1, [str(p) for p in summaries]
    summary = json.loads(summaries[0].read_text())
    assert summary["current_run_id"] == str(run_id) or summary["current_run_id"] == run_id
    assert summary["parent_table"] == RAW112_TABLE
    assert summary["parent_theorem"] == RAW112_THEOREM
    assert summary["weighted_bound"] == 100000
    assert summary["full_union_root_modules"] == 93
    assert set(summary["new_retry_groups"]) == {
        "r01a-rest0", "r01a-rest1", "r01a-deep",
        "r04a", "r04b", "r04c", "r05a0", "r05a1",
    }

    parent_manifests = []
    for path in manifests:
        manifest = json.loads(path.read_text())
        roots = {x["module"] for x in manifest.get("roots", [])}
        if "Raw112ClosedCover" in roots:
            parent_manifests.append((path, manifest))
    assert len(parent_manifests) == 1, [str(p) for p, _ in parent_manifests]
    manifest_path, manifest = parent_manifests[0]
    assert manifest["artifact_name"] == RAW112_ARTIFACT
    assert manifest["proof_source_revision"] == run["head_sha"]
    assert "4.36.0-rc2" in manifest["lean_version"]
    modules = {x["module"] for x in manifest["modules"]}
    assert {"Raw112Data", "Raw112ClosedCover"} <= modules
    return dirs, pin, item, summary, manifest_path, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical58-run-id", required=True, type=int)
    parser.add_argument("--raw112-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    raw113_work = work / "raw113-base"
    raw112_work = work / "raw112-parent"
    raw113_work.mkdir()
    raw112_work.mkdir()

    raw113_dirs, raw113_pin, raw113_item, raw113_report = verify_raw113_base(
        raw113_work, args.canonical58_run_id
    )
    raw112_dirs, raw112_pin, raw112_item, raw112_summary, raw112_manifest_path, raw112_manifest = verify_raw112_parent(
        raw112_work, args.raw112_run_id
    )

    linked = work / "linked"
    linked.mkdir()
    copied = []
    raw113_audit = {}
    raw112_audit = {}
    selected.add_family({"root": "Canonical58Raw113Graft"}, raw113_dirs, linked, copied, raw113_audit)
    selected.add_family({"root": "Raw112ClosedCover"}, raw112_dirs, linked, copied, raw112_audit)
    assert (linked / "Canonical58Raw113Graft.olean").is_file()
    assert (linked / "Raw112ClosedCover.olean").is_file()
    env = dict(os.environ, LEAN_PATH=str(linked))

    membership_source = HERE / "Canonical59Raw112Membership.lean"
    membership_output = linked / (membership_source.stem + ".olean")
    assert not membership_output.exists()
    membership_log = a68.compile_module(
        membership_source, membership_output, env, work / "raw112-membership.log"
    )
    membership_profiles = a68.gate(membership_log, [
        MEM + ".p112_source_eq",
        MEM + ".p112_count64",
        MEM + ".p112_count59",
        MEM + ".p112_count58",
        MEM + ".p112_root",
        MEM + ".p112_cover",
    ])

    graft_source = HERE / "Canonical57Raw112Graft.lean"
    graft_output = linked / (graft_source.stem + ".olean")
    assert not graft_output.exists()
    graft_log = a68.compile_module(
        graft_source, graft_output, env, work / "canonical57-raw112-graft.log"
    )
    graft_profiles = a68.gate(graft_log, [
        NS + ".p112_count58",
        NS + ".count57",
        NS + ".raw59_retained",
        NS + ".raw113_removed",
        NS + ".parents_pairwise_distinct",
        NS + ".parents_root",
        NS + ".parents_cover",
        NS + ".sound_integrated",
        NS + ".exact_at_target",
        NS + ".exact_at_champion_score",
    ])

    generated = work / "generated"
    generated.mkdir()
    for source in (
        HERE / "Canonical59Raw112Membership.lean",
        HERE / "Canonical57Raw112Graft.lean",
        HERE / "README.md",
    ):
        shutil.copy2(source, generated / source.name)

    report = {
        "status": "kernel-checked Canonical58-to-57 Raw112 delta after Raw113",
        "canonical59_base_run_id": raw113_report["base_run_id"],
        "canonical58_base_run_id": args.canonical58_run_id,
        "canonical58_artifact_name": raw113_item["name"],
        "canonical58_artifact_id": raw113_pin[0],
        "canonical58_artifact_sha256": raw113_pin[2],
        "canonical58_source_revision": raw113_report["source_revision"],
        "canonical58_olean_sha256": raw113_report["olean_sha256"],
        "canonical58_residual_count": 58,
        "raw113_consumed": True,
        "raw59_retained": True,
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": raw112_item["name"],
        "raw112_artifact_id": raw112_pin[0],
        "raw112_artifact_sha256": raw112_pin[2],
        "raw112_parent_table": RAW112_TABLE,
        "raw112_parent_theorem": RAW112_THEOREM,
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": raw112_summary,
        "raw112_parent_manifest": str(raw112_manifest_path),
        "raw112_parent_manifest_module_count": raw112_manifest["module_count"],
        "raw113_link_audit": raw113_audit,
        "raw112_link_audit": raw112_audit,
        "membership_axioms": membership_profiles,
        "axioms": graft_profiles,
        "remaining_residual_count": 57,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "membership_source_sha256": a68.sha(membership_source),
        "membership_olean_sha256": a68.sha(membership_output),
        "graft_source_sha256": a68.sha(graft_source),
        "graft_olean_sha256": a68.sha(graft_output),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical57-raw112-graft.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
