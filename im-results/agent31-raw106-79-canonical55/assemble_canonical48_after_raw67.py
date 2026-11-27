#!/usr/bin/env python3
"""Consume source-accepted Raw67 after an accepted Canonical49 roster."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "im-results" / "agent31-shared-core"))

import assemble_canonical68 as a68
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
BASE_ARTIFACT_NAME = "canonical49-after-raw59-integrated"
BASE_MODULE = "Canonical49AfterRaw59Graft"
BASE_REPORT = "canonical49-after-raw59.json"
RAW67_ARTIFACT_NAME = "agent31-raw67-parent-source-accepted-reuse"
RAW67_MODULE = "Raw67ParentCover"
NS = "BB6.Agent31Canonical48AfterRaw67"


def find_unique(root: Path, name: str):
    matches = [
        p for p in root.rglob(name)
        if "metadata" not in p.parts
    ]
    assert len(matches) == 1, [str(p) for p in matches]
    return matches[0]


def find_report(work: Path, artifact_id: int, name: str):
    matches = [
        p for p in work.rglob(name)
        if "metadata" not in p.parts
    ]
    if not matches:
        matches = list((work / "metadata" / str(artifact_id)).rglob(name))
    assert len(matches) == 1, [str(p) for p in matches]
    return matches[0]


def verify_canonical49(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", (run_id, run.get("conclusion"))
    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["name"] == BASE_ARTIFACT_NAME]
    assert len(matches) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = matches[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")

    dirs = a68.download((item["id"], run_id, digest), work)
    root = find_unique(work, BASE_MODULE + ".olean").parent
    report_path = find_report(work, item["id"], BASE_REPORT)
    report = json.loads(report_path.read_text())

    assert report["status"] == (
        "source-accepted Canonical56-to-49 seven-ready-parent delta"
    )
    assert report["source_revision"] == run["head_sha"]
    assert report["canonical56_residual_count"] == 56
    assert report["remaining_residual_count"] == 49
    assert report["raw124_consumed"] and report["raw59_consumed"]
    assert report["raw113_consumed"]
    assert report["all_seven_unique_membership_in_canonical56"]
    assert report["all_seven_pairwise_distinct"]
    assert report["olean_sha256"] == a68.sha(root / (BASE_MODULE + ".olean"))
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return root, item, digest, report_path, report


def verify_raw67(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", (run_id, run.get("conclusion"))
    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["name"] == RAW67_ARTIFACT_NAME]
    assert len(matches) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = matches[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")

    dirs = a68.download((item["id"], run_id, digest), work)
    root = find_unique(work, RAW67_MODULE + ".olean").parent
    report_path = find_report(work, item["id"], "report.json")
    report = json.loads(report_path.read_text())

    assert str(report["raw"]) == "67"
    assert report["source_revision"] == run["head_sha"]
    assert "4.36.0-rc2" in report["lean_version"]
    assert report["parent"]["cover_theorem"] == "BB6.Agent10Raw67.parent_cover"
    assert report["parent"]["bound"] == 808
    assert report["parent"]["table"] == (
        "1RB---_1RC1LB_0RD---_1LD1RE_---0LB_------"
    )
    assert report["raw106_reuse"]["reused_module_count"] > 0
    assert report["compiled_source_module_count"] > 0
    assert "sorryAx" not in str(report["parent"]["axioms"])
    assert "native_decide" not in str(report["parent"]["axioms"])
    return dirs, item, digest, report_path, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical49-run-id", required=True, type=int)
    parser.add_argument("--raw67-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    base_work = work / "base"
    raw67_work = work / "raw67"
    base_work.mkdir()
    raw67_work.mkdir()

    linked, base_item, base_digest, base_report_path, base_report = verify_canonical49(
        base_work, args.canonical49_run_id
    )
    raw67_dirs, raw67_item, raw67_digest, raw67_report_path, raw67_report = (
        verify_raw67(raw67_work, args.raw67_run_id)
    )

    copied = []
    audit = {}
    selected.add_family(
        {"label": "raw67", "root": RAW67_MODULE},
        raw67_dirs,
        linked,
        copied,
        audit,
    )
    assert (linked / (RAW67_MODULE + ".olean")).is_file()

    source = HERE / "Canonical48AfterRaw67Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(
        source, output, env, work / "canonical48-after-raw67.log"
    )
    required = [
        NS + "." + name for name in (
            "p67_count49", "p67_root", "p67_cover", "count48",
            "p67_removed", "raw59_still_removed", "sound_integrated",
            "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical49-base-report.json")
    shutil.copy2(raw67_report_path, generated / "raw67-parent-report.json")

    report = {
        "status": "source-accepted Canonical49-to-48 Raw67 delta",
        "lean_version": lean_version,
        "canonical49_run_id": args.canonical49_run_id,
        "canonical49_artifact_id": base_item["id"],
        "canonical49_artifact_name": base_item["name"],
        "canonical49_artifact_sha256": base_digest,
        "canonical49_source_revision": base_report["source_revision"],
        "canonical49_residual_count": 49,
        "canonical49_olean_sha256": base_report["olean_sha256"],
        "raw67_run_id": args.raw67_run_id,
        "raw67_artifact_id": raw67_item["id"],
        "raw67_artifact_name": raw67_item["name"],
        "raw67_artifact_sha256": raw67_digest,
        "raw67_source_revision": raw67_report["source_revision"],
        "raw67_weighted_bound": 808,
        "raw67_unique_membership_in_canonical49": True,
        "raw67_removed": True,
        "raw59_still_removed": True,
        "remaining_residual_count": 48,
        "raw67_link_audit": audit,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical48-after-raw67.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
