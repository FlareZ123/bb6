#!/usr/bin/env python3
"""Consume Raw95/103/105 plus source-accepted Raw59 directly after Canonical50."""

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

import assemble_canonical47_sharp_after_eight as c47
import assemble_canonical49_raw59_after_eight as raw59base
import assemble_canonical68 as a68
import assemble_canonical59_raw59_graft as raw59
import assemble_canonical_selected as selected

RAW59_STAGE_RUN = raw59base.RAW59_STAGE_RUN
RAW59_STAGE_ARTIFACT_ID = raw59base.RAW59_STAGE_ARTIFACT_ID
RAW59_STAGE_SHA256 = raw59base.RAW59_STAGE_SHA256
NS = "BB6.Agent31Canonical46SharpPlusRaw59"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical50-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    base_work = work / "base"
    raw59_work = work / "raw59"
    base_work.mkdir()
    raw59_work.mkdir()
    sharp_work = {raw: work / ("raw" + raw) for raw in c47.SPECS}
    for d in sharp_work.values():
        d.mkdir()

    linked, base_item, base_digest, base_report_path, base_report = (
        raw59base.verify_canonical50(base_work, args.canonical50_run_id)
    )

    sharp_meta = {}
    copied = []
    audits = {}
    for raw in ("95", "103", "105"):
        dirs, item, manifest_path, manifest = c47.verify_sharp(raw, sharp_work[raw])
        audit = {}
        selected.add_family(c47.SPECS[raw], dirs, linked, copied, audit)
        audits["raw" + raw] = audit
        sharp_meta[raw] = {
            "artifact_id": item["id"],
            "manifest_path": manifest_path,
            "manifest_sha256": a68.sha(manifest_path),
        }

    raw59_delta = raw59.add_raw59(raw59_work, linked, RAW59_STAGE_RUN)
    assert raw59_delta["run_id"] == RAW59_STAGE_RUN
    assert raw59_delta["artifact_id"] == RAW59_STAGE_ARTIFACT_ID
    assert raw59_delta["artifact_sha256"] == RAW59_STAGE_SHA256
    assert raw59_delta["claim"]["theorem"] == "BB6.Agent32Raw59Exact.cover"
    assert raw59_delta["claim"]["bound"] == 4136171
    assert (linked / "Raw59Exact.olean").is_file()

    source = HERE / "Canonical46SharpPlusRaw59Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(
        source, output, env, work / "canonical46-sharp-plus-raw59.log"
    )

    required = [
        NS + "." + name for name in (
            "p95_count50", "p103_count50", "p105_count50", "p59_count50",
            "parents_pairwise_distinct",
            "p95_cover", "p103_cover", "p105_cover", "p59_cover",
            "count46", "all_new_parents_removed",
            "sound_integrated", "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical50-base-report.json")
    for raw, meta in sharp_meta.items():
        shutil.copy2(meta["manifest_path"], generated / f"raw{raw}-parent-manifest.json")
    shutil.copy2(
        raw59_work / "raw59-link-audit.json",
        generated / "raw59-link-audit.json",
    )

    report = {
        "status": "source-accepted Canonical50-to-46 Raw95+Raw103+Raw105+Raw59 delta",
        "lean_version": lean_version,
        "canonical50_run_id": args.canonical50_run_id,
        "canonical50_artifact_id": base_item["id"],
        "canonical50_artifact_name": base_item["name"],
        "canonical50_artifact_sha256": base_digest,
        "canonical50_source_revision": base_report["source_revision"],
        "canonical50_residual_count": 50,
        "canonical50_olean_sha256": base_report["olean_sha256"],
        "sharp_run_id": c47.SHARP_RUN,
        "sharp_source_revision": c47.SHARP_REVISION,
        "sharp_parents": {
            raw: {**c47.SPECS[raw], **sharp_meta[raw]}
            for raw in ("95", "103", "105")
        },
        "raw59": raw59_delta,
        "raw59_weighted_bound": 4136171,
        "link_audits": audits,
        "all_four_unique_membership_in_canonical50": True,
        "all_four_pairwise_distinct": True,
        "remaining_residual_count": 46,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    report_path = work / "canonical46-sharp-plus-raw59.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    packaged = work / "linked"
    assert not packaged.exists(), packaged
    linked.rename(packaged)
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
