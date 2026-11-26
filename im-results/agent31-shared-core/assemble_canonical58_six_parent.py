#!/usr/bin/env python3
"""Compose Raw113 with the already accepted Canonical59 integration artifact.

This avoids regenerating and recompiling the expensive Raw59 source closure.
The Canonical59 artifact is verified by run, artifact digest, report, and
compiler identity; Raw113 is independently verified by its source manifest.
"""
from pathlib import Path
import argparse
import json
import os
import shutil
import subprocess

import assemble_canonical68 as a68

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

RAW113 = {
    "run_id": 45802897709,
    "revision": "e91b9703f6dd7657d16bb9d428181a657ad14fff",
    "artifact_id": 15108067526,
    "artifact_name": "raw113-parent-proof",
    "digest": "7d3ac590a7b9e562e430a00148616dc37d3eb0304fd1b20e9e3cbd07c611f865",
    "root": "Raw113ParentExact",
    "theorem": "BB6.Agent25Raw113.cover113",
    "table": "1RB---_1RC---_0RD---_1LD1RE_---1RC_------",
    "bound": 2674,
    "size": 175456215,
}


def lean_identity():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler = prefix / "bin" / "lean"
    return version, compiler, a68.sha(compiler)


def download_named(run_id, name, work, expected=None):
    run_info = a68.api_json(f"repos/{a68.REPO}/actions/runs/{run_id}")
    assert run_info["conclusion"] == "success", (run_id, run_info.get("conclusion"))
    artifacts = a68.api_json(
        f"repos/{a68.REPO}/actions/runs/{run_id}/artifacts"
    )["artifacts"]
    matches = [item for item in artifacts if item["name"] == name]
    assert len(matches) == 1, (
        run_id, name, [(item["id"], item["name"]) for item in matches]
    )
    item = matches[0]
    assert not item["expired"], (item["id"], "artifact expired")
    digest = item.get("digest") or ""
    assert digest.startswith("sha256:"), (item["id"], digest)
    if expected is not None:
        assert item["id"] == expected["artifact_id"], (item["id"], expected)
        assert digest == "sha256:" + expected["digest"], (digest, expected)
        assert item["size_in_bytes"] == expected["size"], (
            item["size_in_bytes"], expected["size"]
        )
        assert run_info["head_sha"] == expected["revision"], (
            run_info["head_sha"], expected["revision"]
        )
    dirs = a68.download((item["id"], run_id, digest.removeprefix("sha256:")), work)
    metadata = {
        "run_id": run_id,
        "source_revision": run_info["head_sha"],
        "artifact_id": item["id"],
        "artifact_name": item["name"],
        "artifact_digest": digest,
        "artifact_size": item["size_in_bytes"],
        "workflow_conclusion": run_info["conclusion"],
    }
    return dirs, item, run_info, metadata


def verify_raw113(work, version, compiler_sha):
    dirs, item, run_info, metadata = download_named(
        RAW113["run_id"], RAW113["artifact_name"], work, RAW113
    )
    manifest_paths = list((work / "metadata" / str(item["id"])).rglob("manifest.json"))
    assert len(manifest_paths) == 1, [str(path) for path in manifest_paths]
    manifest_path = manifest_paths[0]
    manifest = json.loads(manifest_path.read_text())
    claim = manifest["claim"]
    assert claim["theorem"] == RAW113["theorem"], claim
    assert claim["parent_table"] == RAW113["table"], claim
    assert claim["weighted_bound"] == RAW113["bound"], claim
    assert manifest["proof_source_revision"] == RAW113["revision"], (
        manifest["proof_source_revision"], RAW113["revision"]
    )
    assert manifest["lean_version"] == version, manifest["lean_version"]
    assert manifest["lean_binary"]["sha256"] == compiler_sha
    assert any((directory / "Raw113ParentExact.olean").is_file() for directory in dirs), dirs
    metadata.update({
        "root": RAW113["root"],
        "theorem": claim["theorem"],
        "parent_table": claim["parent_table"],
        "weighted_bound": claim["weighted_bound"],
        "manifest_sha256": a68.sha(manifest_path),
    })
    return dirs, metadata


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--work", required=True)
    parser.add_argument("--canonical59-run-id", type=int, required=True)
    args = parser.parse_args()

    work = Path(args.work).resolve()
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    version, compiler, compiler_sha = lean_identity()

    # Reuse the fully linked, source-audited 5-parent artifact. Its report is
    # included in the artifact and is preserved by assemble_canonical68.download.
    five_dirs, five_item, five_run, five_metadata = download_named(
        args.canonical59_run_id, "canonical59-five-parent-integrated", work
    )
    five_report_paths = list(
        (work / "metadata" / str(five_item["id"])).rglob(
            "canonical59-five-parent-integration.json"
        )
    )
    assert len(five_report_paths) == 1, [str(path) for path in five_report_paths]
    five_report_path = five_report_paths[0]
    five_report = json.loads(five_report_path.read_text())
    assert five_run["head_sha"] == five_report["source_revision"], (
        five_run["head_sha"], five_report["source_revision"]
    )
    assert five_report["status"].startswith(
        "source-audited conditional 64-to-59"
    ), five_report["status"]
    assert five_report["base_residual_count"] == 64
    assert five_report["consumed_parent_count"] == 5
    assert five_report["remaining_residual_count"] == 59
    assert five_report["lean_version"] == version
    assert five_report["compiler_sha256"] == compiler_sha

    linked59_candidates = [
        directory for directory in five_dirs
        if (directory / "Canonical64Raw120Integrated.olean").is_file()
    ]
    assert len(linked59_candidates) == 1, five_dirs
    linked59 = linked59_candidates[0]
    for module in (
        "Canonical64Raw120Integrated",
        "Canonical59FiveParentIntegrated",
        "Raw58Exact",
        "Raw59Exact",
        "Raw108Closed",
        "Raw115Data",
        "Raw119Data",
        "TM63RawUpperInterface",
        "ChampionScoreLowerBound",
    ):
        assert (linked59 / f"{module}.olean").is_file(), module
    assert a68.sha(linked59 / "Canonical64Raw120Integrated.olean") == five_report[
        "canonical64_olean_sha256"
    ]
    assert a68.sha(linked59 / "Canonical59FiveParentIntegrated.olean") == five_report[
        "integration_olean_sha256"
    ]

    # Exact roster membership is evaluated against the same Canonical64 object
    # that the accepted 5-parent integration consumed.
    membership_source = HERE / "Canonical58SixParentMembership.lean"
    membership_output = linked59 / "Canonical58SixParentMembership.olean"
    membership_log = work / "membership-preflight.log"
    membership_env = dict(os.environ, LEAN_PATH=str(linked59))
    membership_text = a68.compile_module(
        membership_source, membership_output, membership_env, membership_log
    )
    assert "sorryAx" not in membership_text and "native_decide" not in membership_text
    membership_required = [
        "BB6.Agent31Canonical58Membership.p58_count64",
        "BB6.Agent31Canonical58Membership.p59_count64",
        "BB6.Agent31Canonical58Membership.p108_count64",
        "BB6.Agent31Canonical58Membership.p113_count64",
        "BB6.Agent31Canonical58Membership.p115_count64",
        "BB6.Agent31Canonical58Membership.p119_count64",
        "BB6.Agent31Canonical58Membership.count58",
        "BB6.Agent31Canonical58Membership.parents_root",
    ]
    membership_axioms = a68.gate(membership_text, membership_required)
    print("Membership preflight passed: six unique exact parents, 58 retained.", flush=True)

    raw113_dirs, raw113_metadata = verify_raw113(work, version, compiler_sha)

    # Re-link the existing five-parent kernel objects with Raw113. Every
    # duplicate is checked by the strict kernel-data comparator.
    linked58 = work / "linked58"
    families = [
        (
            "canonical59-five-parent-base",
            [linked59],
            [
                "Canonical64Raw120Integrated",
                "Canonical58SixParentMembership",
                "Raw58Exact",
                "Raw59Exact",
                "Raw108Closed",
                "Raw115Data",
                "Raw119Data",
                "TM63RawUpperInterface",
                "ChampionScoreLowerBound",
            ],
        ),
        ("raw113", raw113_dirs, ["Raw113ParentExact"]),
    ]
    a68.link_reachable([[linked59], raw113_dirs], work, linked58, families=families)

    source = HERE / "Canonical58SixParentIntegrated.lean"
    output = linked58 / "Canonical58SixParentIntegrated.olean"
    integration_log = work / "canonical58-six-parent.log"
    integration_env = dict(os.environ, LEAN_PATH=str(linked58))
    integration_text = a68.compile_module(
        source, output, integration_env, integration_log
    )
    assert "sorryAx" not in integration_text and "native_decide" not in integration_text
    required = [
        "BB6.Agent31Canonical58SixParentIntegrated.p58_source_eq",
        "BB6.Agent31Canonical58SixParentIntegrated.p59_source_eq",
        "BB6.Agent31Canonical58SixParentIntegrated.p108_source_eq",
        "BB6.Agent31Canonical58SixParentIntegrated.p113_source_eq",
        "BB6.Agent31Canonical58SixParentIntegrated.p115_source_eq",
        "BB6.Agent31Canonical58SixParentIntegrated.p119_source_eq",
        "BB6.Agent31Canonical58SixParentIntegrated.p58_cover",
        "BB6.Agent31Canonical58SixParentIntegrated.p59_cover",
        "BB6.Agent31Canonical58SixParentIntegrated.p108_cover",
        "BB6.Agent31Canonical58SixParentIntegrated.p113_cover",
        "BB6.Agent31Canonical58SixParentIntegrated.p115_cover",
        "BB6.Agent31Canonical58SixParentIntegrated.p119_cover",
        "BB6.Agent31Canonical58SixParentIntegrated.parents_pairwise_distinct",
        "BB6.Agent31Canonical58SixParentIntegrated.parents_cover",
        "BB6.Agent31Canonical58SixParentIntegrated.sound58_integrated",
        "BB6.Agent31Canonical58SixParentIntegrated.exact_at_target",
        "BB6.Agent31Canonical58SixParentIntegrated.exact_at_champion_score",
        "BB6.Agent31Canonical58Membership.p113_count64",
        "BB6.Agent31Canonical58Membership.count58",
    ]
    integration_axioms = a68.gate(integration_text, required)

    report = {
        "status": (
            "source-audited conditional 64-to-58 Canonical64 quotient reduction; "
            "not an exact BB(6) decision"
        ),
        "base_residual_count": 64,
        "consumed_parent_count": 6,
        "remaining_residual_count": 58,
        "common_weighted_floor": 6766859,
        "parent_artifacts": five_report["parent_artifacts"] + [raw113_metadata],
        "canonical59_integration_artifact": five_metadata,
        "canonical59_integration_report_sha256": a68.sha(five_report_path),
        "canonical59_source_revision": five_report["source_revision"],
        "base_precompiled_manifest": five_report["base_precompiled_manifest"],
        "raw59_rebuild": five_report["raw59_rebuild"],
        "canonical64_run_id": five_report["canonical64_run_id"],
        "canonical64_artifact_id": five_report["canonical64_artifact_id"],
        "canonical64_source_revision": five_report["canonical64_source_revision"],
        "canonical64_source_blob_sha": five_report["canonical64_source_blob_sha"],
        "canonical64_olean_sha256": five_report["canonical64_olean_sha256"],
        "canonical64_axioms": five_report["canonical64_axioms"],
        "membership_preflight_axioms": membership_axioms,
        "membership_source_sha256": a68.sha(membership_source),
        "membership_olean_sha256": a68.sha(membership_output),
        "champion_source_profiles": five_report["champion_source_profiles"],
        "integration_axioms": integration_axioms,
        "integration_source_sha256": a68.sha(source),
        "integration_olean_sha256": a68.sha(output),
        "champion_closure_manifest_sha256": five_report[
            "champion_closure_manifest_sha256"
        ],
        "base_reachable_link_audit_sha256": five_report[
            "base_reachable_link_audit_sha256"
        ],
        "reachable_link_audit_sha256": a68.sha(work / "reachable-link-audit.json"),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "lean_version": version,
        "compiler_sha256": compiler_sha,
        "conditional_exactness": {
            "theorem": (
                "BB6.Agent31Canonical58SixParentIntegrated.exact_at_champion_score"
            ),
            "score": "proposedTM63Moves + 7",
            "remaining_hypotheses": (
                "Cover (WeightedBound (proposedTM63Moves + 7)) for each of the "
                "58 retained representatives"
            ),
            "champion_lower_bound": "6766859 <= proposedTM63Moves + 7",
            "champion_witness": "BB6Coverage.Agent48DirectRoot.champion_raw_witness",
        },
    }
    report_path = work / "canonical58-six-parent-integration.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print(
        "Six accepted parent Covers composed in the exact Canonical64 core; "
        "58 residual Covers remain.",
        flush=True,
    )


if __name__ == "__main__":
    main()
