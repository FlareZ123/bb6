#!/usr/bin/env python3
"""Consume source-accepted Raw67 after the Canonical46 sharp+Raw59 successor."""

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
sys.path.insert(0, str(HERE))

import assemble_canonical68 as a68
import assemble_canonical_selected as selected
import assemble_canonical51_after_raw67 as raw67base

REPO = "FlareZ123/bb6"
BASE_ARTIFACT_NAME = "canonical46-raw59-after-sharp-integrated"
BASE_MODULE = "Canonical46Raw59AfterSharpGraft"
BASE_REPORT = "canonical46-raw59-after-sharp.json"
NS = "BB6.Agent31Canonical45Raw67AfterSharpRaw59"


def find_unique(root: Path, name: str):
    matches = [p for p in root.rglob(name) if "metadata" not in p.parts]
    assert len(matches) == 1, (name, [str(p) for p in matches])
    return matches[0]


def find_report(work: Path, artifact_id: int, name: str):
    matches = [p for p in work.rglob(name) if "metadata" not in p.parts]
    if not matches:
        matches = list((work / "metadata" / str(artifact_id)).rglob(name))
    assert len(matches) == 1, (name, [str(p) for p in matches])
    return matches[0]


def verify_canonical46(work: Path, run_id: int):
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

    a68.download((item["id"], run_id, digest), work)
    root = find_unique(work, BASE_MODULE + ".olean").parent
    report_path = find_report(work, item["id"], BASE_REPORT)
    report = json.loads(report_path.read_text())

    assert report["status"] == "source-accepted Canonical47-to-46 Raw59 delta"
    assert report["source_revision"] == run["head_sha"]
    assert report["canonical47_residual_count"] == 47
    assert report["remaining_residual_count"] == 46
    assert report["raw59_weighted_bound"] == 4136171
    assert report["raw59_unique_membership_in_canonical47"]
    assert report["raw59_removed"]
    assert report["olean_sha256"] == a68.sha(root / (BASE_MODULE + ".olean"))
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return root, item, digest, report_path, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical46-run-id", required=True, type=int)
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

    linked, base_item, base_digest, base_report_path, base_report = verify_canonical46(
        base_work, args.canonical46_run_id
    )
    raw67_dirs, raw67_item, raw67_digest, raw67_report_path, raw67_report = (
        raw67base.verify_raw67(raw67_work, args.raw67_run_id)
    )

    copied = []
    audit = {}
    selected.add_family(
        {"label": "raw67", "root": raw67base.RAW67_MODULE},
        raw67_dirs,
        linked,
        copied,
        audit,
    )
    assert (linked / (raw67base.RAW67_MODULE + ".olean")).is_file()

    source = HERE / "Canonical45Raw67AfterSharpRaw59Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(
        source, output, env, work / "canonical45-raw67-after-sharp-raw59.log"
    )
    required = [
        NS + "." + name for name in (
            "p67_count46", "p67_root", "p67_cover", "count45",
            "p67_removed", "raw59_still_removed", "sound_integrated",
            "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical46-base-report.json")
    shutil.copy2(raw67_report_path, generated / "raw67-parent-report.json")

    report = {
        "status": "source-accepted Canonical46-to-45 Raw67 delta",
        "lean_version": lean_version,
        "canonical46_run_id": args.canonical46_run_id,
        "canonical46_artifact_id": base_item["id"],
        "canonical46_artifact_name": base_item["name"],
        "canonical46_artifact_sha256": base_digest,
        "canonical46_source_revision": base_report["source_revision"],
        "canonical46_residual_count": 46,
        "canonical46_olean_sha256": base_report["olean_sha256"],
        "raw67_run_id": args.raw67_run_id,
        "raw67_artifact_id": raw67_item["id"],
        "raw67_artifact_name": raw67_item["name"],
        "raw67_artifact_sha256": raw67_digest,
        "raw67_source_revision": raw67_report["source_revision"],
        "raw67_weighted_bound": 808,
        "raw67_unique_membership_in_canonical46": True,
        "raw67_removed": True,
        "raw59_still_removed": True,
        "remaining_residual_count": 45,
        "raw67_link_audit": audit,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    report_path = work / "canonical45-raw67-after-sharp-raw59.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    packaged = work / "linked"
    assert not packaged.exists(), packaged
    linked.rename(packaged)
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
