#!/usr/bin/env python3
"""Directly remove four source-accepted ready parents from accepted Canonical57."""

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

NS = "BB6.Agent31Canonical53FourReadyParents"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
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

    linked, base_item, base_report_path, base_report = c55.verify_base(base_work)

    parent_reports = {}
    family_inputs = []

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
        link_audits[spec["label"] if "label" in spec else spec["root"]] = audit

    source = HERE / "Canonical53FourReadyParentsGraft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log_path = work / "canonical53-four-ready-parents.log"
    log = a68.compile_module(source, output, env, log_path)

    required = [
        NS + "." + name for name in (
            "p106_count57", "p79_count57", "p83_count57", "p85_count57",
            "parents_pairwise_distinct",
            "p106_root", "p79_root", "p83_root", "p85_root",
            "p106_cover", "p79_cover", "p83_cover", "p85_cover",
            "count53", "all_ready_parents_removed",
            "sound_integrated", "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical57-base-report.json")
    for name, (path, _) in parent_reports.items():
        shutil.copy2(path, generated / (name + "-parent-report.json"))
    shutil.copy2(raw85_manifest_path, generated / "raw85-parent-manifest.json")
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(c53.RAW83, indent=2, sort_keys=True) + "\n"
    )

    report = {
        "status": "source-accepted direct Canonical57-to-53 four-ready-parent delta",
        "lean_version": lean_version,
        "canonical57_run_id": c55.BASE_RUN,
        "canonical57_artifact_id": c55.BASE_ARTIFACT_ID,
        "canonical57_artifact_name": base_item["name"],
        "canonical57_artifact_sha256": c55.BASE_ARTIFACT_SHA,
        "canonical57_source_revision": c55.BASE_SOURCE_REVISION,
        "canonical57_residual_count": 57,
        "canonical57_olean_sha256": a68.sha(
            linked / "Raw124Canonical58Membership.olean"
        ),
        "parents": {
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
        "all_four_unique_membership_in_canonical57": True,
        "all_four_pairwise_distinct": True,
        "raw124_already_removed": True,
        "remaining_residual_count": 53,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical53-four-ready-parents.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
