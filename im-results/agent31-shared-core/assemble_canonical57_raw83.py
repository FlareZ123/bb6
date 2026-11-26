#!/usr/bin/env python3
"""Compose the source-accepted Raw83 Cover with the accepted Canonical58 core.

This extends the one-owner Canonical64 chain from 58 to 57 residual parents.
It reuses the accepted six-parent artifact and Raw83's independently accepted
source closure; it does not regenerate any of the seven parent Covers.
"""
from pathlib import Path
import argparse
import json
import os
import shutil
import subprocess

import assemble_canonical58_six_parent as a58
import assemble_canonical68 as a68

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

RAW83 = {
    "run_id": 45755362807,
    "revision": "8d8a3fcc59600146fb25eb70afc2f34a31c99cb3",
    "artifact_id": 15087730774,
    "artifact_name": "raw83-parent-proof",
    "digest": "89ea0f6ae8f0da2d11f86c959b1d848d7c4ef44e933899bfc2654c7dc1a9a1a2",
    "theorem": "BB6.Agent10Raw83.all_completions",
    "table": "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA",
    "bound": 514,
    "size": 9709805,
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--work", required=True)
    parser.add_argument("--canonical58-run-id", type=int, required=True)
    args = parser.parse_args()

    work = Path(args.work).resolve()
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    version, compiler, compiler_sha = a58.lean_identity()

    # Reuse the accepted 58-parent core, whose report records the exact
    # Canonical64 base, six parent Covers, source revision and compiler.
    canonical58_dirs, canonical58_item, canonical58_run, canonical58_metadata = (
        a58.download_named(
            args.canonical58_run_id,
            "canonical58-six-parent-integrated",
            work,
        )
    )
    canonical58_reports = list(
        (work / "metadata" / str(canonical58_item["id"])).rglob(
            "canonical58-six-parent-integration.json"
        )
    )
    assert len(canonical58_reports) == 1, [str(p) for p in canonical58_reports]
    canonical58_report_path = canonical58_reports[0]
    canonical58_report = json.loads(canonical58_report_path.read_text())
    assert canonical58_run["head_sha"] == canonical58_report["source_revision"]
    assert canonical58_report["status"].startswith(
        "source-audited conditional 64-to-58"
    ), canonical58_report["status"]
    assert canonical58_report["base_residual_count"] == 64
    assert canonical58_report["consumed_parent_count"] == 6
    assert canonical58_report["remaining_residual_count"] == 58
    assert canonical58_report["lean_version"] == version
    assert canonical58_report["compiler_sha256"] == compiler_sha

    linked58_candidates = [
        directory for directory in canonical58_dirs
        if (directory / "Canonical58SixParentIntegrated.olean").is_file()
    ]
    assert len(linked58_candidates) == 1, canonical58_dirs
    linked58 = linked58_candidates[0]
    for module in (
        "Canonical64Raw120Integrated",
        "Canonical58SixParentMembership",
        "Canonical58SixParentIntegrated",
        "Raw58Exact",
        "Raw59Exact",
        "Raw108Closed",
        "Raw113ParentExact",
        "Raw115Data",
        "Raw119Data",
        "TM63RawUpperInterface",
        "ChampionScoreLowerBound",
    ):
        assert (linked58 / f"{module}.olean").is_file(), module
    assert a68.sha(linked58 / "Canonical64Raw120Integrated.olean") == (
        canonical58_report["canonical64_olean_sha256"]
    )
    assert a68.sha(linked58 / "Canonical58SixParentIntegrated.olean") == (
        canonical58_report["integration_olean_sha256"]
    )

    # Raw83's 514 Cover is a separate source-accepted artifact. Pin its exact
    # run, source revision, artifact ID, digest, size, Lean version and binary.
    raw83_dirs, raw83_item, raw83_run, raw83_metadata = a58.download_named(
        RAW83["run_id"], RAW83["artifact_name"], work, RAW83
    )
    raw83_manifest_paths = list(
        (work / "metadata" / str(raw83_item["id"])).rglob("manifest.json")
    )
    assert len(raw83_manifest_paths) == 1, [
        str(path) for path in raw83_manifest_paths
    ]
    raw83_manifest_path = raw83_manifest_paths[0]
    raw83_manifest = json.loads(raw83_manifest_path.read_text())
    assert raw83_manifest["claim"]["theorem"] == RAW83["theorem"]
    assert raw83_manifest["proof_source_revision"] == RAW83["revision"]
    assert raw83_manifest["lean_version"] == version
    assert raw83_manifest["lean_binary"]["sha256"] == compiler_sha
    assert raw83_manifest["module_count"] == 93
    raw83_roots = [
        directory for directory in raw83_dirs
        if (directory / "A10Raw83Exact.olean").is_file()
    ]
    assert len(raw83_roots) == 1, raw83_dirs
    raw83_metadata.update({
        "root": "A10Raw83Exact",
        "theorem": RAW83["theorem"],
        "parent_table": RAW83["table"],
        "weighted_bound": RAW83["bound"],
        "manifest_sha256": a68.sha(raw83_manifest_path),
    })

    # Strict-link the exact Canonical58 and Raw83 kernel closures. The Raw83
    # membership source is then compiled against this same linked Canonical58
    # object, not against a competing roster or a stale preflight object.
    linked57 = work / "linked57"
    families = [
        (
            "canonical58-base",
            [linked58],
            [
                "Canonical64Raw120Integrated",
                "Canonical58SixParentMembership",
                "Canonical58SixParentIntegrated",
                "Raw58Exact",
                "Raw59Exact",
                "Raw108Closed",
                "Raw113ParentExact",
                "Raw115Data",
                "Raw119Data",
                "TM63RawUpperInterface",
                "ChampionScoreLowerBound",
            ],
        ),
        ("raw83", raw83_dirs, ["A10Raw83Exact"]),
    ]
    a68.link_reachable([ [linked58], raw83_dirs ], work, linked57, families=families)

    membership_env = dict(os.environ, LEAN_PATH=str(linked57))
    raw83_membership_source = (
        ROOT / "im-results" / "agent29-raw83-membership"
        / "Raw83Canonical58Membership.lean"
    )
    raw83_membership_output = linked57 / "Raw83Canonical58Membership.olean"
    raw83_membership_log = work / "raw83-canonical58-membership.log"
    raw83_membership_text = a68.compile_module(
        raw83_membership_source,
        raw83_membership_output,
        membership_env,
        raw83_membership_log,
    )
    assert "sorryAx" not in raw83_membership_text
    assert "native_decide" not in raw83_membership_text
    raw83_membership_required = [
        "BB6.Agent29Raw83Canonical58Membership.p83_root",
        "BB6.Agent29Raw83Canonical58Membership.p83_count58",
        "BB6.Agent29Raw83Canonical58Membership.p83_distinct_from_six",
        "BB6.Agent29Raw83Canonical58Membership.p83_exact_count58",
        "BB6.Agent29Raw83Canonical58Membership.p83_exact_distinct_from_six",
    ]
    raw83_membership_axioms = a68.gate(
        raw83_membership_text, raw83_membership_required
    )

    membership_source = HERE / "Canonical57Raw83Membership.lean"
    membership_output = linked57 / "Canonical57Raw83Membership.olean"
    membership_log = work / "canonical57-membership.log"
    membership_text = a68.compile_module(
        membership_source, membership_output, membership_env, membership_log
    )
    assert "sorryAx" not in membership_text
    assert "native_decide" not in membership_text
    membership_required = [
        "BB6.Agent31Canonical57Membership.p83_count58",
        "BB6.Agent31Canonical57Membership.p83_distinct_from_six",
        "BB6.Agent31Canonical57Membership.count57",
        "BB6.Agent31Canonical57Membership.p83_root",
    ]
    membership_axioms = a68.gate(membership_text, membership_required)

    integration_source = HERE / "Canonical57Raw83Integrated.lean"
    integration_output = linked57 / "Canonical57Raw83Integrated.olean"
    integration_log = work / "canonical57-integration.log"
    integration_text = a68.compile_module(
        integration_source, integration_output, membership_env, integration_log
    )
    assert "sorryAx" not in integration_text
    assert "native_decide" not in integration_text
    integration_required = [
        "BB6.Agent31Canonical57Integrated.p83_source_eq",
        "BB6.Agent31Canonical57Integrated.p83_cover",
        "BB6.Agent31Canonical57Integrated.sound57_integrated",
        "BB6.Agent31Canonical57Integrated.exact_at_target",
        "BB6.Agent31Canonical57Integrated.exact_at_champion_score",
    ]
    integration_axioms = a68.gate(integration_text, integration_required)

    report = {
        "status": (
            "source-audited conditional 64-to-57 Canonical64 quotient reduction; "
            "not an exact BB(6) decision"
        ),
        "base_residual_count": 64,
        "consumed_parent_count": 7,
        "remaining_residual_count": 57,
        "common_weighted_floor": 6766859,
        "parent_artifacts": (
            canonical58_report["parent_artifacts"] + [raw83_metadata]
        ),
        "canonical58_integration_artifact": canonical58_metadata,
        "canonical58_integration_report_sha256": a68.sha(
            canonical58_report_path
        ),
        "canonical58_source_revision": canonical58_report["source_revision"],
        "canonical58_integration_olean_sha256": a68.sha(
            linked58 / "Canonical58SixParentIntegrated.olean"
        ),
        "canonical64_run_id": canonical58_report["canonical64_run_id"],
        "canonical64_artifact_id": canonical58_report["canonical64_artifact_id"],
        "canonical64_source_revision": canonical58_report[
            "canonical64_source_revision"
        ],
        "canonical64_olean_sha256": canonical58_report[
            "canonical64_olean_sha256"
        ],
        "raw83_source_revision": RAW83["revision"],
        "raw83_artifact": raw83_metadata,
        "raw83_exact_weighted_maximum": RAW83["bound"],
        "raw83_membership_axioms": raw83_membership_axioms,
        "raw83_membership_source_sha256": a68.sha(raw83_membership_source),
        "raw83_membership_olean_sha256": a68.sha(raw83_membership_output),
        "membership_axioms": membership_axioms,
        "membership_source_sha256": a68.sha(membership_source),
        "membership_olean_sha256": a68.sha(membership_output),
        "integration_axioms": integration_axioms,
        "integration_source_sha256": a68.sha(integration_source),
        "integration_olean_sha256": a68.sha(integration_output),
        "reachable_link_audit_sha256": a68.sha(
            work / "reachable-link-audit.json"
        ),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "lean_version": version,
        "compiler_sha256": compiler_sha,
        "conditional_exactness": {
            "theorem": (
                "BB6.Agent31Canonical57Integrated.exact_at_champion_score"
            ),
            "score": "proposedTM63Moves + 7",
            "remaining_hypotheses": (
                "Cover (WeightedBound (proposedTM63Moves + 7)) for each of the "
                "57 retained representatives"
            ),
            "champion_lower_bound": "6766859 <= proposedTM63Moves + 7",
            "champion_witness": "BB6Coverage.Agent48DirectRoot.champion_raw_witness",
        },
    }
    report_path = work / "canonical57-raw83-integration.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print(
        "Seven accepted parent Covers composed in the exact Canonical64 core; "
        "57 residual Covers remain.",
        flush=True,
    )


if __name__ == "__main__":
    main()
