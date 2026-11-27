#!/usr/bin/env python3
"""Consume Raw106/79/83/85 after an accepted Raw124+Raw59 Canonical56."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "im-results" / "agent31-shared-core"))

import assemble_canonical55 as c55
import assemble_canonical53 as c53
import assemble_canonical68 as a68
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
BASE_ARTIFACT_NAME = "canonical56-raw59-after-raw124-integrated"
BASE_MODULE = "Raw59Canonical56AfterRaw124"
BASE_REPORT = "canonical56-raw59-after-raw124.json"
NS = "BB6.Agent31Canonical52AfterRaw59"


def verify_base(work: Path, run_id: int):
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
    roots = [
        p for p in work.rglob(BASE_MODULE + ".olean")
        if "metadata" not in p.parts
    ]
    assert len(roots) == 1, [str(p) for p in roots]
    linked = roots[0].parent

    reports = [
        p for p in work.rglob(BASE_REPORT)
        if "metadata" not in p.parts
    ]
    if not reports:
        reports = list((work / "metadata" / str(item["id"])).rglob(BASE_REPORT))
    assert len(reports) == 1, [str(p) for p in reports]
    report_path = reports[0]
    report = json.loads(report_path.read_text())

    assert report["status"] == "source-accepted Canonical57-Raw124 to Canonical56-Raw59 graft"
    assert report["source_revision"] == run["head_sha"]
    assert report["canonical58_residual_count"] == 58
    assert report["canonical57_residual_count"] == 57
    assert report["remaining_residual_count"] == 56
    assert report["raw113_consumed"] and report["raw124_consumed"]
    assert report["raw59_consumed"] and report["raw124_removed"]
    assert report["olean_sha256"] == a68.sha(linked / (BASE_MODULE + ".olean"))
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return linked, item, digest, report_path, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical56-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    base_work = work / "base"
    raw106_work = work / "raw106"
    raw79_work = work / "raw79"
    raw83_work = work / "raw83"
    raw85_work = work / "raw85"
    for d in (base_work, raw106_work, raw79_work, raw83_work, raw85_work):
        d.mkdir()

    linked, base_item, base_digest, base_report_path, base_report = verify_base(
        base_work, args.canonical56_run_id
    )

    family_inputs = []
    parent_reports = {}
    for raw, parent_work in (("106", raw106_work), ("79", raw79_work)):
        dirs, report_path, report = c55.verify_parent(raw, parent_work)
        family_inputs.append((c55.PARENTS[raw], dirs))
        parent_reports["raw" + raw] = (report_path, report)

    raw83_dirs, raw83_metadata = five.download_parent(c53.RAW83, raw83_work)
    family_inputs.append((c53.RAW83, raw83_dirs))

    raw85_dirs, raw85_manifest_path, raw85_manifest = c53.verify_raw85(raw85_work)
    family_inputs.append((c53.RAW85, raw85_dirs))

    copied = []
    link_audits = {}
    for spec, dirs in family_inputs:
        audit = {}
        selected.add_family(spec, dirs, linked, copied, audit)
        link_audits[spec["label"]] = audit

    source = HERE / "Canonical52AfterRaw59Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(
        source, output, env, work / "canonical52-after-raw59.log"
    )

    required = [
        NS + "." + name for name in (
            "p106_count56", "p79_count56", "p83_count56", "p85_count56",
            "parents_pairwise_distinct",
            "p106_cover", "p79_cover", "p83_cover", "p85_cover",
            "count52", "all_four_removed",
            "raw59_still_removed", "raw124_still_removed", "raw113_still_removed",
            "sound_integrated", "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical56-base-report.json")
    for name, (path, _) in parent_reports.items():
        shutil.copy2(path, generated / (name + "-parent-report.json"))
    shutil.copy2(raw85_manifest_path, generated / "raw85-parent-manifest.json")
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(c53.RAW83, indent=2, sort_keys=True) + "\n"
    )

    report = {
        "status": "source-accepted Canonical56-to-52 Raw106+Raw79+Raw83+Raw85 delta",
        "lean_version": lean_version,
        "canonical56_run_id": args.canonical56_run_id,
        "canonical56_artifact_id": base_item["id"],
        "canonical56_artifact_name": base_item["name"],
        "canonical56_artifact_sha256": base_digest,
        "canonical56_source_revision": base_report["source_revision"],
        "canonical56_residual_count": 56,
        "canonical56_olean_sha256": base_report["olean_sha256"],
        "raw124_consumed": True,
        "raw59_consumed": True,
        "raw113_consumed": True,
        "parents": {
            "raw106": {**c55.PARENTS["106"], "run_id": c55.PARENT_RUN},
            "raw79": {**c55.PARENTS["79"], "run_id": c55.PARENT_RUN},
            "raw83": {**c53.RAW83, "metadata": raw83_metadata},
            "raw85": c53.RAW85,
        },
        "link_audits": link_audits,
        "all_four_unique_membership_in_canonical56": True,
        "all_four_pairwise_distinct": True,
        "remaining_residual_count": 52,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical52-after-raw59.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
