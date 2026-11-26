#!/usr/bin/env python3
"""Source-audit Raw118's exact unique membership in the accepted Canonical64 roster.

This is a membership gate only. It does not remove Raw118, create a competing
roster, or claim a global BB(6) upper bound.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
SHARED = ROOT / "im-results" / "agent31-shared-core"
sys.path.insert(0, str(SHARED))
import assemble_canonical63 as a63  # noqa: E402

a68 = a63.a68

RAW118_RUN = 45812415227
RAW118_REVISION = "b2e050ea75b4633f06ce836375a4260135ed500c"
RAW118_ARTIFACT = 15120592642
RAW118_ARTIFACT_NAME = "raw118-parent-proof"
RAW118_ARTIFACT_DIGEST = "226a16e1181a456a2f6eddfb785b3882abde05d462837fffcb4b3ba47dfe2053"
RAW118_PARENT_BOUND = 756496
RAW118_PARENT_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---0LE_------"

SOURCE_BLOBS = {
    "Raw118Base.lean": "12fbdc8ece046ead083352dfcd8307abe6ba7a9d",
    "Raw118Complete.lean": "58d764e67fec267e42de4f41d8a3cee044963063",
    "Raw118Canonical64Membership.lean": "313254cfbfea0cd96d49ad4329df296c03cd05dd",
}

MEMBERSHIP_THEOREMS = [
    "BB6.Agent16Raw118Canonical64Membership.p118_eq_raw118_parent",
    "BB6.Agent16Raw118Canonical64Membership.p118_root",
    "BB6.Agent16Raw118Canonical64Membership.p118_parent_count64",
]


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def git_blob(path):
    return subprocess.check_output(
        ["git", "hash-object", str(path)], cwd=ROOT, text=True
    ).strip()


def verify_raw118_parent_artifact(work):
    run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{RAW118_RUN}")
    assert run["conclusion"] == "success", run
    assert run["head_sha"] == RAW118_REVISION, (run["head_sha"], RAW118_REVISION)
    artifact = a68.api_json(f"repos/{a68.REPO}/actions/artifacts/{RAW118_ARTIFACT}")
    assert artifact["name"] == RAW118_ARTIFACT_NAME, artifact
    assert artifact["workflow_run"]["id"] == RAW118_RUN, artifact
    assert artifact["digest"] == "sha256:" + RAW118_ARTIFACT_DIGEST, artifact
    assert not artifact["expired"], artifact
    return a68.download(
        (RAW118_ARTIFACT, RAW118_RUN, RAW118_ARTIFACT_DIGEST), work
    ), {
        "run_id": RAW118_RUN,
        "source_revision": RAW118_REVISION,
        "artifact_id": RAW118_ARTIFACT,
        "artifact_name": RAW118_ARTIFACT_NAME,
        "artifact_digest": "sha256:" + RAW118_ARTIFACT_DIGEST,
        "parent_table": RAW118_PARENT_TABLE,
        "parent_bound": RAW118_PARENT_BOUND,
        "accepted_theorem": "BB6.Agent1Raw118Complete.parent_cover",
        "accepted_exactness_theorem": "BB6.Agent1Raw118Complete.parent_exact",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version

    raw118_dirs, raw118_parent = verify_raw118_parent_artifact(work)
    for name, expected in SOURCE_BLOBS.items():
        path = ROOT / "im-results" / "agent16-raw118" / name
        actual = git_blob(path)
        assert actual == expected, (name, actual, expected)

    # Canonical64 is reconstructed from its two full pinned dependency bundles;
    # its small published audit artifact is verified for provenance by a63.
    parts = a63.download_canonical64_parts(work)
    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        ("raw118-parent", raw118_dirs, ["Raw118Complete"])
    ]
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"], raw118_dirs],
        work,
        linked,
        families=families,
    )

    # The Raw118 parent artifact supplies Raw118Base.olean. Reusing this exact
    # object, and strictly comparing every overlapping import, preserves the
    # identity of the parent definition used by the accepted Cover.
    for module in ("Raw118Complete", "Raw118Base", "Raw111Prefix"):
        assert (linked / f"{module}.olean").is_file(), module

    env = dict(os.environ, LEAN_PATH=str(linked))
    canonical64_output, canonical64_log, canonical64_axioms = (
        a63.compile_canonical64(linked, env, work)
    )

    membership_source = ROOT / "im-results" / "agent16-raw118" / "Raw118Canonical64Membership.lean"
    membership_output = linked / "Raw118Canonical64Membership.olean"
    membership_log = a68.compile_module(
        membership_source,
        membership_output,
        env,
        work / "raw118-membership.log",
    )
    if re.search(r"sorryAx|native_decide", membership_log):
        raise AssertionError("forbidden proof mechanism in Raw118 Canonical64 membership")
    membership_axioms = a68.gate(membership_log, MEMBERSHIP_THEOREMS)

    output = work / "output"
    output.mkdir()
    for name in (
        "Canonical64Raw120Integrated.olean",
        "Raw118Complete.olean",
        "Raw118Base.olean",
        "Raw118Canonical64Membership.olean",
        "kernel-link-manifest.json",
    ):
        shutil.copy2(linked / name, output / name)
    for name in (
        "reachable-link-audit.json",
        "canonical64.log",
        "raw118-membership.log",
    ):
        shutil.copy2(work / name, output / name)
    for name in (
        "Raw118Base.lean",
        "Raw118Complete.lean",
        "Raw118Canonical64Membership.lean",
    ):
        shutil.copy2(ROOT / "im-results" / "agent16-raw118" / name, output / name)
    shutil.copy2(
        ROOT / "im-results" / "agent3-tnf-raw120" / "Canonical64Raw120Integrated.lean",
        output / "Canonical64Raw120Integrated.lean",
    )

    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    report = {
        "status": (
            "source-audited exact unique Raw118 membership in the accepted "
            "Canonical64 roster; membership only, not an integrated roster cut"
        ),
        "membership_theorem": MEMBERSHIP_THEOREMS[-1],
        "parent_table": RAW118_PARENT_TABLE,
        "membership_count": 1,
        "base_residual_count": 64,
        "no_global_cut_claim": True,
        "raw118_parent_cover": raw118_parent,
        "canonical64_base": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "artifact_name": a63.CANONICAL64_NAME,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "source_revision": a63.CANONICAL64_REVISION,
            "source_blob_sha": a63.CANONICAL64_SOURCE_BLOB_SHA,
            "recompiled_olean_sha256": sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "source_blobs": SOURCE_BLOBS,
        "lean_version": version,
        "compiler_sha256": sha(prefix / "bin" / "lean"),
        "raw118_membership_axioms": membership_axioms,
        "reachable_link_audit_sha256": sha(work / "reachable-link-audit.json"),
        "kernel_link_manifest_sha256": sha(linked / "kernel-link-manifest.json"),
    }
    report_path = output / "report.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print(
        "Raw118's exact unique membership in Canonical64 passed the strict "
        "source/olean link and standard-axiom gates. No roster cut was made.",
        flush=True,
    )


if __name__ == "__main__":
    main()
