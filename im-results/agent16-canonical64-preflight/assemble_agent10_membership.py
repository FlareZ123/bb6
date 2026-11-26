#!/usr/bin/env python3
"""Strictly combine the three independently source-accepted Agent10 parent Covers.

This final stage checks exact Canonical64 membership and pairwise distinctness.
It does not remove roster entries; that belongs to Agent31's coordinated
Canonical64 consumer.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import assemble_agent10_canonical64 as common

ROOT = common.ROOT
GEN = common.GEN
HELPER = common.HELPER
SOURCE_BLOBS = common.SOURCE_BLOBS
PARENTS = common.PARENTS
MEMBERSHIP_THEOREMS = common.MEMBERSHIP_THEOREMS
a63 = common.a63
a68 = common.a68

PARENT_ROOTS = {
    "106": ["Raw106ParentCover", "Raw106Attainment"],
    "79": ["Raw79ParentCover", "Raw79Attainment"],
    "67": ["Raw67ParentCover", "Raw67Attainment"],
}
PARENT_GATE_THEOREMS = [
    "BB6.Agent10Raw106.parent_cover",
    "BB6.Agent10Raw106.exact_weighted_threshold",
    "BB6.Agent10Raw79.parent_cover",
    "BB6.Agent10Raw79.exact_weighted_threshold",
    "BB6.Agent10Raw67.parent_cover",
    "BB6.Agent10Raw67.exact_weighted_threshold",
]


def verify_parent_artifact(raw, directory, compiler_sha, source_revision):
    directory = Path(directory).resolve()
    report_path = directory / "report.json"
    if not report_path.is_file():
        raise FileNotFoundError(report_path)
    report = json.loads(report_path.read_text())
    assert report["raw"] == raw, (raw, report.get("raw"))
    assert report["source_revision"] == source_revision, (
        raw, report["source_revision"], source_revision
    )
    assert report["compiler_sha256"] == compiler_sha, raw
    assert report["no_global_cut_claim"] is True, raw
    parent = report["parent"]
    assert parent["table"] == PARENTS[raw]["table"], raw
    assert parent["bound"] == PARENTS[raw]["bound"], raw
    assert parent["cover_theorem"] == f"BB6.Agent10Raw{raw}.parent_cover", raw
    assert parent["exactness_theorem"] == f"BB6.Agent10Raw{raw}.exact_weighted_threshold", raw
    assert set(parent["source_files"]) == {
        f"Raw{raw}Attainment.lean", f"Raw{raw}ParentCover.lean"
    }, raw
    for name, expected in parent["source_files"].items():
        assert expected == SOURCE_BLOBS[name], (raw, name, expected)
        assert common.git_blob(GEN / name) == expected, (raw, name)
    source_dir = directory / f"source-{raw}"
    manifest_path = source_dir / "source-manifest.json"
    assert manifest_path.is_file(), manifest_path
    assert common.sha(manifest_path) == parent["source_export_manifest_sha256"], raw
    manifest = json.loads(manifest_path.read_text())
    assert manifest["root"] == f"Raw{raw}Data", raw
    assert manifest["proof_source_revision"] == source_revision, raw
    parent_dir = directory / "parent-olean-closure"
    assert parent_dir.is_dir(), parent_dir
    for root in PARENT_ROOTS[raw]:
        assert common.module_file(parent_dir, root).is_file(), (raw, root)
    return report, parent_dir


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--raw106", type=Path, required=True)
    parser.add_argument("--raw79", type=Path, required=True)
    parser.add_argument("--raw67", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler_sha = common.sha(prefix / "bin" / "lean")
    source_revision = common.git_revision(ROOT)

    artifact_dirs = {
        "106": args.raw106.resolve(),
        "79": args.raw79.resolve(),
        "67": args.raw67.resolve(),
    }
    reports = {}
    parent_dirs = {}
    for raw in ("106", "79", "67"):
        reports[raw], parent_dirs[raw] = verify_parent_artifact(
            raw, artifact_dirs[raw], compiler_sha, source_revision
        )
        canonical = reports[raw]["canonical64"]
        assert canonical["run_id"] == a63.CANONICAL64_RUN, raw
        assert canonical["artifact_id"] == a63.CANONICAL64_ARTIFACT, raw
        assert canonical["artifact_name"] == a63.CANONICAL64_NAME, raw
        assert canonical["artifact_digest"] == "sha256:" + a63.CANONICAL64_DIGEST, raw
        assert canonical["source_revision"] == a63.CANONICAL64_REVISION, raw

    parts = a63.download_canonical64_parts(work)
    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        (f"agent10-raw{raw}", [parent_dirs[raw]], PARENT_ROOTS[raw])
        for raw in ("106", "79", "67")
    ]
    a68.link_reachable(
        [
            parts["canonical65"],
            parts["raw120"],
            parent_dirs["106"],
            parent_dirs["79"],
            parent_dirs["67"],
        ],
        work,
        linked,
        families=families,
    )

    linked_env = dict(os.environ, LEAN_PATH=str(linked))
    canonical64_output, canonical64_log, canonical64_axioms = (
        a63.compile_canonical64(linked, linked_env, work)
    )
    membership_output = linked / "Agent10Canonical64Membership.olean"
    membership_log = a68.compile_module(
        HELPER,
        membership_output,
        linked_env,
        work / "agent10-membership.log",
    )
    all_theorems = PARENT_GATE_THEOREMS + MEMBERSHIP_THEOREMS
    membership_axioms = a68.gate(membership_log, all_theorems)

    output = work / "output"
    output.mkdir()
    for raw in ("106", "79", "67"):
        shutil.copytree(parent_dirs[raw], output / f"parent-olean-closure-raw{raw}")
        shutil.copytree(
            artifact_dirs[raw] / f"source-{raw}",
            output / f"source-{raw}",
        )
        for name in (f"Raw{raw}Attainment.lean", f"Raw{raw}ParentCover.lean"):
            shutil.copy2(artifact_dirs[raw] / name, output / name)
        shutil.copy2(artifact_dirs[raw] / "report.json", output / f"raw{raw}-parent-report.json")

    shutil.copy2(canonical64_output, output / "Canonical64Raw120Integrated.olean")
    shutil.copy2(membership_output, output / "Agent10Canonical64Membership.olean")
    shutil.copy2(linked / "kernel-link-manifest.json", output / "kernel-link-manifest.json")
    shutil.copy2(work / "reachable-link-audit.json", output / "reachable-link-audit.json")
    shutil.copy2(work / "canonical64.log", output / "canonical64.log")
    shutil.copy2(work / "agent10-membership.log", output / "agent10-membership.log")
    shutil.copy2(HELPER, output / HELPER.name)
    shutil.copy2(
        ROOT / "im-results" / "agent3-tnf-raw120" / "Canonical64Raw120Integrated.lean",
        output / "Canonical64Raw120Integrated.lean",
    )

    report = {
        "status": (
            "source-accepted Raw106/79/67 exact parent Covers and unique Canonical64 "
            "membership; no roster cut or global upper-bound claim"
        ),
        "source_revision": source_revision,
        "lean_version": lean_version,
        "compiler_sha256": compiler_sha,
        "canonical64": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "artifact_name": a63.CANONICAL64_NAME,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "source_revision": a63.CANONICAL64_REVISION,
            "source_blob_sha": a63.CANONICAL64_SOURCE_BLOB_SHA,
            "recompiled_olean_sha256": common.sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "parents": {
            raw: {
                **PARENTS[raw],
                "cover_theorem": f"BB6.Agent10Raw{raw}.parent_cover",
                "exactness_theorem": f"BB6.Agent10Raw{raw}.exact_weighted_threshold",
                "membership_theorem": (
                    f"BB6.Agent16Agent10Canonical64Membership.p{raw}_parent_count64"
                ),
                "membership_count": 1,
                "parent_axioms": reports[raw]["parent"]["axioms"],
                "source_export_manifest_sha256": (
                    reports[raw]["parent"]["source_export_manifest_sha256"]
                ),
            }
            for raw in ("106", "79", "67")
        },
        "membership_axioms": membership_axioms,
        "strict_link_audit_sha256": common.sha(work / "reachable-link-audit.json"),
        "kernel_link_manifest_sha256": common.sha(linked / "kernel-link-manifest.json"),
        "helper_source_blob_sha": common.git_blob(HELPER),
        "pairwise_distinct": True,
        "no_global_cut_claim": True,
    }
    (output / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print(
        "Raw106/79/67 parent Covers and exact unique Canonical64 memberships "
        "passed the strict source/object/axiom gates. No roster cut was made.",
        flush=True,
    )


if __name__ == "__main__":
    main()
