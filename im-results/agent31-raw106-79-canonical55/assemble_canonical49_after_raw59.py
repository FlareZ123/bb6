#!/usr/bin/env python3
"""Consume seven accepted ready parents after an accepted Raw124+Raw59 Canonical56."""

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

import assemble_canonical52_after_raw59 as c52
import assemble_canonical50_from58 as c50
import assemble_canonical55 as c55
import assemble_canonical53 as c53
import assemble_canonical68 as a68
import assemble_canonical59_five_parent as five_parent
import assemble_canonical_selected as selected

NS = "BB6.Agent31Canonical49AfterRaw59"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical56-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    names = ["base","raw106","raw79","raw83","raw85","raw69","raw73","raw78"]
    wd = {name: work / name for name in names}
    for d in wd.values():
        d.mkdir()

    linked, base_item, base_digest, base_report_path, base_report = c52.verify_base(
        wd["base"], args.canonical56_run_id
    )

    family_inputs = []
    metadata_paths = {}
    for raw in ("106","79"):
        dirs, report_path, report = c55.verify_parent(raw, wd["raw"+raw])
        family_inputs.append((c55.PARENTS[raw], dirs))
        metadata_paths["raw"+raw] = report_path

    raw83_dirs, raw83_metadata = five_parent.download_parent(c53.RAW83, wd["raw83"])
    family_inputs.append((c53.RAW83, raw83_dirs))

    raw85_dirs, raw85_manifest_path, raw85_manifest = c53.verify_raw85(wd["raw85"])
    family_inputs.append((c53.RAW85, raw85_dirs))
    metadata_paths["raw85"] = raw85_manifest_path

    legacy_meta = {}
    for raw in ("69","73","78"):
        dirs, item, manifest_path, manifest = c50.verify_legacy(raw, wd["raw"+raw])
        family_inputs.append((c50.LEGACY[raw], dirs))
        metadata_paths["raw"+raw] = manifest_path
        legacy_meta[raw] = {"artifact_id": item["id"], "manifest": manifest}

    copied = []
    link_audits = {}
    for spec, dirs in family_inputs:
        audit = {}
        selected.add_family(spec, dirs, linked, copied, audit)
        link_audits[spec["label"]] = audit

    source = HERE / "Canonical49AfterRaw59Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(source, output, env, work / "canonical49-after-raw59.log")

    required = [
        NS + "." + name for name in (
            "p106_count56","p79_count56","p83_count56","p85_count56",
            "p69_count56","p73_count56","p78_count56","parents_pairwise_distinct",
            "p106_cover","p79_cover","p83_cover","p85_cover",
            "p69_cover","p73_cover","p78_cover",
            "count49","all_seven_removed","raw59_still_removed",
            "raw124_still_removed","raw113_still_removed",
            "sound_integrated","exact_at_target","exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical56-base-report.json")
    for label, path in metadata_paths.items():
        shutil.copy2(path, generated / (label + "-metadata.json"))
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(c53.RAW83, indent=2, sort_keys=True) + "\n"
    )

    report = {
        "status": "source-accepted Canonical56-to-49 seven-ready-parent delta",
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
            **{"raw"+raw: c50.LEGACY[raw] for raw in ("69","73","78")},
        },
        "link_audits": link_audits,
        "all_seven_unique_membership_in_canonical56": True,
        "all_seven_pairwise_distinct": True,
        "remaining_residual_count": 49,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git","rev-parse","HEAD"], text=True
        ).strip(),
    }
    (work / "canonical49-after-raw59.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
