#!/usr/bin/env python3
"""Compose the accepted Raw113 Canonical58 base with the accepted Raw112 parent Cover."""
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
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
NS = "BB6.Agent17Canonical57Raw112Graft"
MEM = "BB6.Agent17Canonical59Raw112Membership"
RAW113_ARTIFACT = "canonical58-raw113-graft-integrated"
RAW112_ARTIFACT = "raw112-closed-parent-cover"
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"


def verify_raw113_base(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    candidates = [x for x in artifacts if x["name"] == RAW113_ARTIFACT]
    assert len(candidates) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = candidates[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")
    pin = (item["id"], run_id, digest)
    dirs = a68.download(pin, work)
    roots = [p for p in dirs if (p / "Canonical58Raw113Graft.olean").is_file()]
    assert len(roots) == 1, [str(p) for p in roots]

    metadata = work / "metadata" / str(item["id"])
    reports = list(metadata.rglob("canonical58-raw113-graft.json"))
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["base_run_id"] == 45880290680
    assert report["base_residual_count"] == 59
    assert report["remaining_residual_count"] == 58
    assert report["raw59_retained"]
    assert report["source_revision"] == run["head_sha"]
    assert report["olean_sha256"] == a68.sha(roots[0] / "Canonical58Raw113Graft.olean")
    profiles = [report["membership_axioms"], report["axioms"]]
    assert "sorryAx" not in str(profiles)
    assert "native_decide" not in str(profiles)
    return dirs, pin, item, report


def verify_raw112_parent(work: Path, run_id: int):
    # The accepted Raw112 parent artifact intentionally separates the frozen
    # proof-source checkout from the later assembly-repair workflow revision.
    # Generic download_named_artifact assumes equality and therefore rejects
    # the valid accepted run 46146501930.  Verify both provenance layers
    # explicitly here instead of weakening the shared generic rule.
    expected_proof_source = "6b8232d51d93665f66808b7faff7457963174aca"
    expected_assembly_revision = "8da8090eab8f85670300b44eabf65070793864d7"

    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", (run_id, run.get("conclusion"))
    assert run["head_sha"] == expected_assembly_revision, (
        run["head_sha"], expected_assembly_revision
    )
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    matches = [x for x in artifacts if x["name"] == RAW112_ARTIFACT]
    assert len(matches) == 1, [
        (x["id"], x["name"]) for x in artifacts
    ]
    item = matches[0]
    assert not item["expired"] and item["digest"].startswith("sha256:"), item
    digest = item["digest"].removeprefix("sha256:")
    dirs = a68.download((item["id"], run_id, digest), work)

    metadata_dir = work / "metadata" / str(item["id"])
    manifests = []
    for path in metadata_dir.rglob("manifest.json"):
        try:
            manifest = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        claim = manifest.get("claim") or {}
        modules = {entry.get("module") for entry in manifest.get("modules", [])}
        if (claim.get("theorem") == RAW112_THEOREM
                and claim.get("parent_table") == RAW112_TABLE
                and claim.get("weighted_bound") == 100000
                and {"Raw112ClosedCover", "Raw112Data"} <= modules):
            manifests.append((path, manifest))
    assert len(manifests) == 1, [str(p) for p, _ in manifests]
    manifest_path, manifest = manifests[0]
    assert manifest["proof_source_revision"] == expected_proof_source, (
        manifest["proof_source_revision"], expected_proof_source
    )
    assert "4.36.0-rc2" in manifest["lean_version"], manifest["lean_version"]
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert manifest["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")

    summaries = list(metadata_dir.rglob("retry-summary.json"))
    assert len(summaries) == 1, [str(p) for p in summaries]
    summary = json.loads(summaries[0].read_text())
    assert summary["current_run_id"] == str(run_id) or summary["current_run_id"] == run_id
    assert summary["parent_table"] == RAW112_TABLE
    assert summary["parent_theorem"] == RAW112_THEOREM
    assert summary["weighted_bound"] == 100000
    assert summary["full_union_root_modules"] == 93
    all_retry_groups = {
        "r01a-rest0", "r01a-rest1", "r01a-deep",
        "r04a", "r04b", "r04c", "r05a0", "r05a1",
    }
    new_retry_groups = set(summary["new_retry_groups"])
    reused_retry_groups = set(summary.get("reused_retry_groups", []))
    assert new_retry_groups and not (new_retry_groups & reused_retry_groups)
    assert new_retry_groups | reused_retry_groups == all_retry_groups
    resumed_ids = summary.get("resumed_from_retry_run_ids")
    if resumed_ids is None:
        resumed_from = summary.get("resumed_from_retry_run_id")
        resumed_ids = [] if resumed_from is None else [resumed_from]
    assert isinstance(resumed_ids, list)
    assert all(isinstance(source_run_id, int) and source_run_id > 0
               for source_run_id in resumed_ids)
    if not resumed_ids:
        assert new_retry_groups == all_retry_groups and not reused_retry_groups
    else:
        assert reused_retry_groups
    assert any((d / "Raw112ClosedCover.olean").is_file() for d in dirs)

    metadata = {
        "run_id": run_id,
        "source_revision": expected_proof_source,
        "assembly_revision": run["head_sha"],
        "artifact_id": item["id"],
        "artifact_name": item["name"],
        "artifact_digest": item["digest"],
        "manifest_path": str(manifest_path),
        "manifest_sha256": a68.sha(manifest_path),
        "theorem": RAW112_THEOREM,
        "parent_table": RAW112_TABLE,
        "weighted_bound": 100000,
        "lean_version": manifest["lean_version"],
        "lean_binary_sha256": manifest["lean_binary"]["sha256"],
        "module_count": manifest["module_count"],
    }
    print(
        "Verified Raw112 parent artifact "
        f"{item['id']} with frozen proof source {expected_proof_source} "
        f"and assembly revision {run['head_sha']}.",
        flush=True,
    )
    return metadata, dirs, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical58-run-id", required=True, type=int)
    parser.add_argument("--raw112-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    raw113_work = work / "raw113-base"
    raw112_work = work / "raw112-parent"
    raw113_work.mkdir()
    raw112_work.mkdir()

    raw113_dirs, raw113_pin, raw113_item, raw113_report = verify_raw113_base(
        raw113_work, args.canonical58_run_id
    )
    raw112_meta, raw112_dirs, raw112_summary = verify_raw112_parent(
        raw112_work, args.raw112_run_id
    )

    linked = work / "linked"
    linked.mkdir()
    copied = []
    raw113_audit = {}
    raw112_audit = {}
    selected.add_family({"root": "Canonical58Raw113Graft"}, raw113_dirs, linked, copied, raw113_audit)
    selected.add_family({"root": "Raw112ClosedCover"}, raw112_dirs, linked, copied, raw112_audit)
    assert (linked / "Canonical58Raw113Graft.olean").is_file()
    assert (linked / "Raw112ClosedCover.olean").is_file()
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
        MEM + ".p112_count58",
        MEM + ".p112_root",
        MEM + ".p112_cover",
    ])

    graft_source = HERE / "Canonical57Raw112Graft.lean"
    graft_output = linked / (graft_source.stem + ".olean")
    assert not graft_output.exists()
    graft_log = a68.compile_module(
        graft_source, graft_output, env, work / "canonical57-raw112-graft.log"
    )
    graft_profiles = a68.gate(graft_log, [
        NS + ".p112_count58",
        NS + ".count57",
        NS + ".raw59_retained",
        NS + ".raw113_removed",
        NS + ".parents_pairwise_distinct",
        NS + ".parents_root",
        NS + ".parents_cover",
        NS + ".sound_integrated",
        NS + ".exact_at_target",
        NS + ".exact_at_champion_score",
    ])

    generated = work / "generated"
    generated.mkdir()
    for source in (
        HERE / "Canonical59Raw112Membership.lean",
        HERE / "Canonical57Raw112Graft.lean",
        HERE / "README.md",
    ):
        shutil.copy2(source, generated / source.name)

    report = {
        "status": "kernel-checked Canonical58-to-57 Raw112 delta after Raw113",
        "canonical59_base_run_id": raw113_report["base_run_id"],
        "canonical58_base_run_id": args.canonical58_run_id,
        "canonical58_artifact_name": raw113_item["name"],
        "canonical58_artifact_id": raw113_pin[0],
        "canonical58_artifact_sha256": raw113_pin[2],
        "canonical58_source_revision": raw113_report["source_revision"],
        "canonical58_olean_sha256": raw113_report["olean_sha256"],
        "canonical58_residual_count": 58,
        "raw113_consumed": True,
        "raw59_retained": True,
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": raw112_meta["artifact_name"],
        "raw112_artifact_id": raw112_meta["artifact_id"],
        "raw112_artifact_sha256": raw112_meta["artifact_digest"],
        "raw112_parent_table": RAW112_TABLE,
        "raw112_parent_theorem": RAW112_THEOREM,
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": raw112_summary,
        "raw112_parent_manifest": raw112_meta["manifest_path"],
        "raw112_parent_manifest_module_count": raw112_meta["module_count"],
        "raw113_link_audit": raw113_audit,
        "raw112_link_audit": raw112_audit,
        "membership_axioms": membership_profiles,
        "axioms": graft_profiles,
        "remaining_residual_count": 57,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "membership_source_sha256": a68.sha(membership_source),
        "membership_olean_sha256": a68.sha(membership_output),
        "graft_source_sha256": a68.sha(graft_source),
        "graft_olean_sha256": a68.sha(graft_output),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical57-raw112-graft.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
