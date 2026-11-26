#!/usr/bin/env python3
"""Consume Raw59 directly into the accepted Canonical58 Raw113 delta.

This is the Raw59-first alternative to Canonical56Raw59Graft: it preserves the
accepted Canonical58 base, links the independent Raw59 slice with the strict
shared-object/kernel-equality audit, and proves the exact 57-entry complement.
No Canonical57/56 claim is made unless the corresponding source artifacts pass.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))

import assemble_canonical68 as a68
import assemble_canonical59_raw59_graft as raw59

REPO = "FlareZ123/bb6"
BASE_ARTIFACT = "canonical58-raw113-graft-integrated"
BASE_MODULE = "Canonical58Raw113Graft"
NS = "BB6.Agent32Canonical57Raw59Graft"


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

    choices = [
        root for root in dirs
        if (root / f"{BASE_MODULE}.olean").is_file()
    ]
    assert len(choices) == 1, [str(p) for p in choices]
    linked = choices[0]

    reports = list(
        (work / "metadata" / str(item["id"])).rglob("canonical58-raw113-graft.json")
    )
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["source_revision"] == run["head_sha"]
    assert report["base_residual_count"] == 59
    assert report["remaining_residual_count"] == 58
    assert report["raw59_retained"] is True
    assert report["raw113_parent"], "Canonical58 report lacks the consumed Raw113 parent"
    assert report["raw113_link_audit"], "Canonical58 report lacks its Raw113 link audit"
    assert report["olean_sha256"] == a68.sha(linked / f"{BASE_MODULE}.olean")
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return linked, pin, item, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical58-run-id", required=True, type=int)
    parser.add_argument("--raw59-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    linked, base_pin, base_artifact, base_report = verify_base(
        work, args.canonical58_run_id
    )
    raw59_delta = raw59.add_raw59(work, linked, args.raw59_run_id)
    env = dict(os.environ, LEAN_PATH=str(linked))

    source = HERE / "Canonical57Raw59Graft.lean"
    output = linked / f"{source.stem}.olean"
    assert not output.exists()
    log = a68.compile_module(
        source, output, env, work / "canonical57-raw59-graft.log"
    )
    profiles = a68.gate(log, [NS + "." + name for name in (
        "p59_count58", "p59_count57", "count57", "raw113_removed",
        "parents_pairwise_distinct", "parents_root", "parents_cover",
        "sound_integrated", "exact_at_target", "exact_at_champion_score",
    )])

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    (generated / "canonical58-base-report.json").write_text(
        json.dumps(base_report, indent=2) + "\n"
    )

    report = {
        "status": "kernel-checked Canonical58-to-57 Raw59 delta",
        "canonical58_run_id": args.canonical58_run_id,
        "canonical58_artifact_name": base_artifact["name"],
        "canonical58_artifact_id": base_pin[0],
        "canonical58_artifact_sha256": base_pin[2],
        "canonical58_source_revision": base_report["source_revision"],
        "canonical58_olean_sha256": base_report["olean_sha256"],
        "base_residual_count": 58,
        "raw113_consumed": True,
        "raw113_parent": base_report["raw113_parent"],
        "raw59_run_id": args.raw59_run_id,
        "raw59_parent": raw59_delta,
        "raw59_consumed": True,
        "raw59_weighted_bound": raw59_delta["claim"]["bound"],
        "remaining_residual_count": 57,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical57-raw59-graft.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
