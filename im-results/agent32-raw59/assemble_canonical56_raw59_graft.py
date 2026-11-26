#!/usr/bin/env python3
"""Consume Raw59 after the accepted Raw113→Raw112 Canonical57 chain.

The Canonical57 base and the independently accepted Raw59 slice are pinned by
workflow run/artifact metadata. Only the Raw59 import closure is added to the
base; duplicate kernel objects are compared before the final Lean consumer is
compiled. This script is an intermediate integration path until both inputs
are accepted.
"""
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
import assemble_canonical59_raw59_graft as raw59

REPO = "FlareZ123/bb6"
BASE_ARTIFACT = "canonical57-raw112-graft-integrated"
BASE_MODULE = "Canonical57Raw112Graft"
NS = "BB6.Agent32Canonical56Raw59Graft"


def verify_base(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["name"] == BASE_ARTIFACT]
    assert len(matches) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = matches[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")
    pin = (item["id"], run_id, digest)
    dirs = a68.download(pin, work)

    choices = []
    for root in dirs:
        for candidate in (root, root / "linked"):
            if (candidate / f"{BASE_MODULE}.olean").is_file():
                choices.append(candidate)
    assert len(choices) == 1, [str(p) for p in choices]
    linked = choices[0]

    reports = list(
        (work / "metadata" / str(item["id"])).rglob("canonical57-raw112-graft.json")
    )
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["source_revision"] == run["head_sha"]
    assert report["canonical58_residual_count"] == 58
    assert report["remaining_residual_count"] == 57
    assert report["raw113_consumed"] and report["raw59_retained"]
    canonical58_olean = linked / "Canonical58Raw113Graft.olean"
    assert canonical58_olean.is_file()
    assert report["canonical58_olean_sha256"] == a68.sha(canonical58_olean)
    assert report["raw112_parent_theorem"] == "BB6.Agent47Raw112.parent_cover"
    assert report["raw112_parent_table"] == "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
    assert report["raw112_weighted_bound"] == 100000
    assert report["graft_olean_sha256"] == a68.sha(
        linked / f"{BASE_MODULE}.olean"
    )
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return linked, pin, item, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical57-run-id", required=True, type=int)
    parser.add_argument("--raw59-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    linked, base_pin, base_artifact, base_report = verify_base(
        work, args.canonical57_run_id
    )
    raw59_delta = raw59.add_raw59(work, linked, args.raw59_run_id)
    env = dict(os.environ, LEAN_PATH=str(linked))

    source = HERE / "Canonical56Raw59Graft.lean"
    output = linked / f"{source.stem}.olean"
    assert not output.exists()
    log = a68.compile_module(
        source, output, env, work / "canonical56-raw59-graft.log"
    )
    profiles = a68.gate(log, [NS + "." + name for name in (
        "p59_count57", "p59_count56", "count56", "raw113_removed",
        "raw112_removed", "parents_pairwise_distinct", "parents_root",
        "parents_cover", "sound_integrated", "exact_at_target",
        "exact_at_champion_score",
    )])

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    (generated / "canonical57-base-report.json").write_text(
        json.dumps(base_report, indent=2) + "\n"
    )

    report = {
        "status": "kernel-checked Canonical57-to-56 Raw59 delta",
        "canonical57_run_id": args.canonical57_run_id,
        "canonical57_artifact_name": base_artifact["name"],
        "canonical57_artifact_id": base_pin[0],
        "canonical57_artifact_sha256": base_pin[2],
        "canonical57_source_revision": base_report["source_revision"],
        "canonical57_olean_sha256": base_report["graft_olean_sha256"],
        "canonical57_residual_count": 57,
        "canonical58_run_id": base_report["canonical58_base_run_id"],
        "canonical58_artifact_id": base_report["canonical58_artifact_id"],
        "canonical58_artifact_sha256": base_report["canonical58_artifact_sha256"],
        "canonical58_olean_sha256": base_report["canonical58_olean_sha256"],
        "raw113_consumed": True,
        "raw112_consumed": True,
        "raw112_parent_run_id": base_report["raw112_run_id"],
        "raw112_parent_artifact_id": base_report["raw112_artifact_id"],
        "raw112_parent_artifact_sha256": base_report["raw112_artifact_sha256"],
        "raw112_parent_theorem": base_report["raw112_parent_theorem"],
        "raw112_parent_table": base_report["raw112_parent_table"],
        "raw112_weighted_bound": base_report["raw112_weighted_bound"],
        "raw59_run_id": args.raw59_run_id,
        "raw59": raw59_delta,
        "raw59_consumed": True,
        "raw113_removed": True,
        "raw112_removed": True,
        "remaining_residual_count": 56,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical56-raw59-graft.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
