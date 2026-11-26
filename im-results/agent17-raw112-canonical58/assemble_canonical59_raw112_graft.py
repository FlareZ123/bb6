#!/usr/bin/env python3
"""Consume the accepted Raw112 parent Cover from the accepted Canonical59 base."""
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
import assemble_canonical59_raw113_graft as raw113_delta
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
NS = "BB6.Agent17Canonical58Raw112Graft"
MEM = "BB6.Agent17Canonical59Raw112Membership"
PARENT_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
PARENT_THEOREM = "BB6.Agent47Raw112.parent_cover"
ARTIFACT_NAME = "raw112-closed-parent-cover"


def verify_raw112(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    candidates = [x for x in artifacts if x["name"] == ARTIFACT_NAME]
    assert len(candidates) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = candidates[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")
    pin = (item["id"], run_id, digest)
    dirs = a68.download(pin, work)
    assert any((d / "Raw112ClosedCover.olean").is_file() for d in dirs)

    metadata = work / "metadata" / str(item["id"])
    summaries = list(metadata.rglob("retry-summary.json"))
    manifests = list(metadata.rglob("manifest.json"))
    assert len(summaries) == 1, [str(p) for p in summaries]
    summary = json.loads(summaries[0].read_text())
    assert summary["current_run_id"] == str(run_id) or summary["current_run_id"] == run_id
    assert summary["parent_table"] == PARENT_TABLE
    assert summary["parent_theorem"] == PARENT_THEOREM
    assert summary["weighted_bound"] == 100000
    assert summary["full_union_root_modules"] == 93
    assert set(summary["new_retry_groups"]) == {
        "r01a-rest0", "r01a-rest1", "r01a-deep",
        "r04a", "r04b", "r04c", "r05a0", "r05a1",
    }

    parent_manifests = []
    for path in manifests:
        manifest = json.loads(path.read_text())
        roots = {x["module"] for x in manifest.get("roots", [])}
        if "Raw112ClosedCover" in roots:
            parent_manifests.append((path, manifest))
    assert len(parent_manifests) == 1, [str(p) for p, _ in parent_manifests]
    manifest_path, manifest = parent_manifests[0]
    assert manifest["artifact_name"] == ARTIFACT_NAME
    assert manifest["proof_source_revision"] == run["head_sha"]
    assert "4.36.0-rc2" in manifest["lean_version"]
    modules = {x["module"] for x in manifest["modules"]}
    assert {"Raw112Data", "Raw112ClosedCover"} <= modules
    return dirs, pin, item, summary, manifest_path, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--base-run-id", required=True, type=int)
    parser.add_argument("--raw112-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    assert args.base_run_id == 45880290680, "use the accepted Canonical59 base"
    base_work = work / "canonical59-base"
    raw_work = work / "raw112-parent"
    base_work.mkdir()
    raw_work.mkdir()
    linked, base_pin, base_artifact, base_report = raw113_delta.verify_base(
        base_work, args.base_run_id
    )
    raw_dirs, raw_pin, raw_artifact, raw_summary, raw_manifest_path, raw_manifest = verify_raw112(
        raw_work, args.raw112_run_id
    )

    copied = []
    link_audit = {}
    selected.add_family({"root": "Raw112ClosedCover"}, raw_dirs, linked, copied, link_audit)
    env = dict(os.environ, LEAN_PATH=str(linked))

    membership_source = HERE / "Canonical59Raw112Membership.lean"
    membership_output = linked / (membership_source.stem + ".olean")
    assert not membership_output.exists()
    membership_log = a68.compile_module(
        membership_source, membership_output, env, work / "raw112-membership.log"
    )
    membership_profiles = a68.gate(membership_log, [
        MEM + ".p112_source_eq",
        MEM + ".p112_count64",
        MEM + ".p112_count59",
        MEM + ".p112_root",
        MEM + ".p112_cover",
    ])

    graft_source = HERE / "Canonical58Raw112Graft.lean"
    graft_output = linked / (graft_source.stem + ".olean")
    assert not graft_output.exists()
    graft_log = a68.compile_module(
        graft_source, graft_output, env, work / "canonical58-raw112-graft.log"
    )
    graft_profiles = a68.gate(graft_log, [
        NS + ".p112_count59",
        NS + ".count58",
        NS + ".raw59_retained",
        NS + ".parents_pairwise_distinct",
        NS + ".parents_root",
        NS + ".parents_cover",
        NS + ".sound_integrated",
        NS + ".exact_at_target",
        NS + ".exact_at_champion_score",
    ])

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(membership_source, generated / membership_source.name)
    shutil.copy2(graft_source, generated / graft_source.name)
    shutil.copy2(HERE / "README.md", generated / "README.md")

    report = {
        "status": "kernel-checked Canonical59-to-58 Raw112 delta",
        "base_run_id": args.base_run_id,
        "base_artifact_name": base_artifact["name"],
        "base_artifact_id": base_pin[0],
        "base_artifact_sha256": base_pin[2],
        "base_source_revision": base_report["source_revision"],
        "base_olean_sha256": base_report["olean_sha256"],
        "base_residual_count": 59,
        "base_accepted": [x["label"] for x in base_report["accepted"]],
        "raw59_retained": True,
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": raw_artifact["name"],
        "raw112_artifact_id": raw_pin[0],
        "raw112_artifact_sha256": raw_pin[2],
        "raw112_parent_table": PARENT_TABLE,
        "raw112_parent_theorem": PARENT_THEOREM,
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": raw_summary,
        "raw112_parent_manifest": str(raw_manifest_path),
        "raw112_parent_manifest_module_count": raw_manifest["module_count"],
        "raw112_link_audit": link_audit,
        "membership_axioms": membership_profiles,
        "axioms": graft_profiles,
        "remaining_residual_count": 58,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "membership_source_sha256": a68.sha(membership_source),
        "membership_olean_sha256": a68.sha(membership_output),
        "graft_source_sha256": a68.sha(graft_source),
        "graft_olean_sha256": a68.sha(graft_output),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical58-raw112-graft.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
