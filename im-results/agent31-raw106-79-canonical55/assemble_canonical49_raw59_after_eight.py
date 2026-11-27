#!/usr/bin/env python3
"""Consume source-accepted Raw59 after an accepted Canonical50 eight-parent roster."""

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
import assemble_canonical59_raw59_graft as raw59

REPO = "FlareZ123/bb6"
BASE_ARTIFACT_NAME = "canonical50-eight-ready-parents-integrated"
BASE_MODULE = "Canonical50EightReadyParentsGraft"
BASE_REPORT = "canonical50-eight-ready-parents.json"

RAW59_STAGE_RUN = 45897242410
RAW59_STAGE_ARTIFACT_ID = 15159864837
RAW59_STAGE_SHA256 = "bb2ac9eb97ac1265a4275b2cfd589f0158d8179bd3cac98cce7a3813b413cee6"

NS = "BB6.Agent31Canonical49Raw59AfterEightReady"


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


def verify_canonical50(work: Path, run_id: int):
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

    assert report["status"] == (
        "source-accepted direct Canonical58-to-50 eight-ready-parent delta"
    )
    assert report["source_revision"] == run["head_sha"]
    assert report["canonical58_residual_count"] == 58
    assert report["remaining_residual_count"] == 50
    assert report["all_eight_unique_membership_in_canonical58"]
    assert report["all_eight_pairwise_distinct"]
    assert report["raw59_retained"]
    assert report["olean_sha256"] == a68.sha(root / (BASE_MODULE + ".olean"))
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return root, item, digest, report_path, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical50-run-id", required=True, type=int)
    parser.add_argument("--raw59-run-id", type=int, default=RAW59_STAGE_RUN)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    base_work = work / "base"
    raw59_work = work / "raw59"
    base_work.mkdir()
    raw59_work.mkdir()

    linked, base_item, base_digest, base_report_path, base_report = verify_canonical50(
        base_work, args.canonical50_run_id
    )

    delta = raw59.add_raw59(raw59_work, linked, args.raw59_run_id)
    assert delta["run_id"] == RAW59_STAGE_RUN, delta
    assert delta["artifact_id"] == RAW59_STAGE_ARTIFACT_ID, delta
    assert delta["artifact_sha256"] == RAW59_STAGE_SHA256, delta
    assert delta["claim"]["theorem"] == "BB6.Agent32Raw59Exact.cover", delta["claim"]
    assert delta["claim"]["bound"] == 4136171, delta["claim"]
    assert (linked / "Raw59Exact.olean").is_file()

    source = HERE / "Canonical49Raw59AfterEightReadyGraft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(
        source, output, env, work / "canonical49-raw59-after-eight-ready.log"
    )
    required = [
        NS + "." + name for name in (
            "p59_count50", "p59_root", "p59_cover", "count49",
            "p59_removed", "sound_integrated", "exact_at_target",
            "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical50-base-report.json")
    shutil.copy2(
        raw59_work / "raw59-link-audit.json",
        generated / "raw59-link-audit.json",
    )

    report = {
        "status": "source-accepted Canonical50-to-49 Raw59 delta",
        "lean_version": lean_version,
        "canonical50_run_id": args.canonical50_run_id,
        "canonical50_artifact_id": base_item["id"],
        "canonical50_artifact_name": base_item["name"],
        "canonical50_artifact_sha256": base_digest,
        "canonical50_source_revision": base_report["source_revision"],
        "canonical50_residual_count": 50,
        "canonical50_olean_sha256": base_report["olean_sha256"],
        "raw59": delta,
        "raw59_weighted_bound": 4136171,
        "raw59_unique_membership_in_canonical50": True,
        "raw59_removed": True,
        "remaining_residual_count": 49,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    report_path = work / "canonical49-raw59-after-eight-ready.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    packaged = work / "linked"
    assert not packaged.exists(), packaged
    linked.rename(packaged)
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
