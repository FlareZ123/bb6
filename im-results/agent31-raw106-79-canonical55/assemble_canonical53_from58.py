#!/usr/bin/env python3
"""Directly remove five source-accepted parents from accepted Canonical58."""

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
sys.path.insert(0, str(ROOT / "im-results" / "agent2-tnf-raw124"))

import assemble_canonical55 as c55
import assemble_canonical53 as c53
import assemble_canonical58_raw83_graft as base58
import assemble_canonical68 as a68
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected
import assemble_raw124_canonical57 as raw124

BASE_RUN = 45891227622
BASE_ARTIFACT_ID = 15151767938
BASE_ARTIFACT_SHA = "b2914335f5bba7b9e410d656d0bcce263738016957af15db814b05442fc5b404"
BASE_ARTIFACT_SIZE = 22949946864
BASE_SOURCE_REVISION = "66cf14dcfba8403f4e2ddc7f7a2d1d85accc90fb"
NS = "BB6.Agent31Canonical53FiveReadyParents"


def verify_base(work: Path):
    linked, pin, item, report = base58.verify_base(work, BASE_RUN)
    assert item["id"] == BASE_ARTIFACT_ID, item["id"]
    assert item["size_in_bytes"] == BASE_ARTIFACT_SIZE, item["size_in_bytes"]
    assert item["digest"] == "sha256:" + BASE_ARTIFACT_SHA, item["digest"]
    assert pin == (BASE_ARTIFACT_ID, BASE_RUN, BASE_ARTIFACT_SHA), pin
    assert report["source_revision"] == BASE_SOURCE_REVISION, report["source_revision"]
    assert report["remaining_residual_count"] == 58
    assert report["raw59_retained"]
    assert "raw118" in report["base_accepted"]
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    report_paths = [
        p for p in work.rglob("canonical58-raw113-graft.json")
        if "metadata" not in p.parts
    ]
    if not report_paths:
        report_paths = list(
            (work / "metadata" / str(item["id"])).rglob(
                "canonical58-raw113-graft.json"
            )
        )
    assert len(report_paths) == 1, [str(p) for p in report_paths]
    return linked, item, report_paths[0], report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    base_work = work / "base"
    raw124_work = work / "raw124"
    raw106_work = work / "raw106"
    raw79_work = work / "raw79"
    raw83_work = work / "raw83"
    raw85_work = work / "raw85"
    for d in (base_work, raw124_work, raw106_work, raw79_work, raw83_work, raw85_work):
        d.mkdir()

    linked, base_item, base_report_path, base_report = verify_base(base_work)

    raw124_item, raw124_dirs, raw124_manifest_path, raw124_manifest = (
        raw124.verify_raw124_parent(raw124.RAW124_RUN, raw124_work)
    )

    family_inputs = [
        ({"label": "raw124", "root": "Raw124ParentComplete"}, raw124_dirs),
    ]
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

    source = HERE / "Canonical53FiveReadyParentsGraft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log_path = work / "canonical53-five-ready-parents.log"
    log = a68.compile_module(source, output, env, log_path)

    required = [
        NS + "." + name for name in (
            "p124_count58", "p106_count58", "p79_count58",
            "p83_count58", "p85_count58", "parents_pairwise_distinct",
            "p124_root", "p106_root", "p79_root", "p83_root", "p85_root",
            "p124_cover", "p106_cover", "p79_cover", "p83_cover", "p85_cover",
            "count53", "all_ready_parents_removed", "raw59_retained",
            "sound_integrated", "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical58-base-report.json")
    shutil.copy2(raw124_manifest_path, generated / "raw124-parent-manifest.json")
    for name, (path, _) in parent_reports.items():
        shutil.copy2(path, generated / (name + "-parent-report.json"))
    shutil.copy2(raw85_manifest_path, generated / "raw85-parent-manifest.json")
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(c53.RAW83, indent=2, sort_keys=True) + "\n"
    )

    report = {
        "status": "source-accepted direct Canonical58-to-53 five-ready-parent delta",
        "lean_version": lean_version,
        "canonical58_run_id": BASE_RUN,
        "canonical58_artifact_id": BASE_ARTIFACT_ID,
        "canonical58_artifact_name": base_item["name"],
        "canonical58_artifact_sha256": BASE_ARTIFACT_SHA,
        "canonical58_source_revision": BASE_SOURCE_REVISION,
        "canonical58_residual_count": 58,
        "canonical58_olean_sha256": base_report["olean_sha256"],
        "parents": {
            "raw124": {
                "run_id": raw124.RAW124_RUN,
                "artifact_id": raw124_item["id"],
                "artifact_name": raw124_item["name"],
                "artifact_sha256": raw124.RAW124_ARTIFACT_SHA,
                "source_revision": raw124.RAW124_SOURCE_REVISION,
                "theorem": "BB6.Agent2Raw124ParentComplete.parent_cover",
                "table": raw124.RAW124_TABLE,
                "bound": raw124.RAW124_BOUND,
            },
            "raw106": {
                **c55.PARENTS["106"],
                "run_id": c55.PARENT_RUN,
                "source_revision": c55.PARENT_SOURCE_REVISION,
            },
            "raw79": {
                **c55.PARENTS["79"],
                "run_id": c55.PARENT_RUN,
                "source_revision": c55.PARENT_SOURCE_REVISION,
            },
            "raw83": {**c53.RAW83, "metadata": raw83_metadata},
            "raw85": c53.RAW85,
        },
        "link_audits": link_audits,
        "all_five_unique_membership_in_canonical58": True,
        "all_five_pairwise_distinct": True,
        "raw59_retained": True,
        "remaining_residual_count": 53,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical53-five-ready-parents.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
