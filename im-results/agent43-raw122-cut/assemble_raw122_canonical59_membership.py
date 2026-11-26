#!/usr/bin/env python3
"""Source-check exact Raw122 membership in the accepted Canonical59 roster.

This is a membership result only. It does not establish the Raw122 parent Cover.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
REPO = "FlareZ123/bb6"
RAW122_CORE_RUN_ID = 45595285735
RAW122_CORE_ARTIFACT_NAME = "raw122-audit-base--1"
RAW122_SOURCE_REF_DEFAULT = "175a9d9004dfadd072d00b5926608f9b4bfdb1d0"

sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))
from assemble_canonical59_raw113_graft import verify_base, a68  # noqa: E402


def sha(path: Path) -> str:
    return a68.sha(path)


def add_raw122_base_dependencies(work: Path, linked: Path):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{RAW122_CORE_RUN_ID}")
    if run.get("conclusion") != "success":
        raise RuntimeError(f"Raw122 core source run is not successful: {run.get('conclusion')}")
    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{RAW122_CORE_RUN_ID}/artifacts"
    )["artifacts"]
    matches = [x for x in artifacts if x["name"] == RAW122_CORE_ARTIFACT_NAME]
    if len(matches) != 1:
        raise RuntimeError(f"expected one {RAW122_CORE_ARTIFACT_NAME} artifact, got {len(matches)}")
    item = matches[0]
    if item.get("expired"):
        raise RuntimeError("Raw122 base artifact has expired")
    digest = item["digest"].removeprefix("sha256:")
    dirs = a68.download((item["id"], RAW122_CORE_RUN_ID, digest), work)

    copied, identical, conflicts = [], [], []
    for root in dirs:
        for source in root.rglob("*.olean"):
            relative = source.relative_to(root)
            if relative.name == "Raw122Base.olean":
                continue
            target = linked / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                left, right = sha(target), sha(source)
                if left == right:
                    identical.append(relative.as_posix())
                else:
                    conflicts.append({
                        "path": relative.as_posix(),
                        "canonical59_sha256": left,
                        "raw122_core_sha256": right,
                        "resolution": "kept-canonical59-object",
                    })
                continue
            shutil.copy2(source, target)
            copied.append(relative.as_posix())

    if not (linked / "Raw111Prefix.olean").is_file():
        raise RuntimeError("Raw122 base artifact did not provide Raw111Prefix.olean")
    return {
        "run_id": RAW122_CORE_RUN_ID,
        "run_head_sha": run.get("head_sha"),
        "artifact_id": item["id"],
        "artifact_name": item["name"],
        "artifact_digest": item["digest"],
        "copied_olean_count": len(copied),
        "identical_duplicate_count": len(identical),
        "conflict_count": len(conflicts),
        "conflicts": conflicts,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--base-run-id", required=True, type=int,
                        help="successful run producing the 59-residual CanonicalSelectedParentIntegrated artifact")
    parser.add_argument("--raw122-source-ref", default=os.environ.get(
        "RAW122_SOURCE_REF", RAW122_SOURCE_REF_DEFAULT))
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    linked, base_pin, base_artifact, base_report = verify_base(work, args.base_run_id)
    raw122_dependencies = add_raw122_base_dependencies(work, linked)

    base_source = HERE / "Raw122Base.lean"
    base_relative = "im-results/agent43-raw122-cut/Raw122Base.lean"
    pinned_source = subprocess.check_output(
        ["git", "show", f"{args.raw122_source_ref}:{base_relative}"], cwd=REPO_ROOT
    )
    pinned_sha = hashlib.sha256(pinned_source).hexdigest()
    current_sha = sha(base_source)
    if pinned_sha != current_sha:
        raise RuntimeError(f"Raw122Base source differs from pinned source: {current_sha} != {pinned_sha}")

    env = dict(os.environ, LEAN_PATH=str(linked))
    compiled = work / "compiled"
    compiled.mkdir()
    base_output = compiled / "Raw122Base.olean"
    a68.compile_module(base_source, base_output, env, work / "raw122-base-source.log")
    shutil.copy2(base_output, linked / "Raw122Base.olean")

    membership_source = HERE / "Raw122Canonical59Membership.lean"
    membership_output = linked / "Raw122Canonical59Membership.olean"
    membership_log = a68.compile_module(
        membership_source, membership_output, env,
        work / "raw122-canonical59-membership.log",
    )
    profiles = a68.gate(membership_log, [
        "BB6.Agent40Raw122Canonical59Membership.p122_source_eq",
        "BB6.Agent40Raw122Canonical59Membership.p122_root",
        "BB6.Agent40Raw122Canonical59Membership.p122_count59",
    ])

    generated = work / "generated"
    generated.mkdir()
    for source in (base_source, membership_source):
        shutil.copy2(source, generated / source.name)
    for output in (linked / "Raw122Base.olean", membership_output):
        shutil.copy2(output, generated / output.name)
    for log_name in ("raw122-base-source.log", "raw122-canonical59-membership.log"):
        shutil.copy2(work / log_name, generated / log_name)

    report = {
        "status": "source-compiled exact unique Raw122 membership in Canonical59",
        "claim_scope": "membership only; Raw122 parent Cover is not established by this artifact",
        "canonical59_run_id": args.base_run_id,
        "canonical59_artifact_id": base_artifact["id"],
        "canonical59_artifact_name": base_artifact["name"],
        "canonical59_artifact_digest": base_artifact["digest"],
        "canonical59_source_revision": base_report["source_revision"],
        "canonical59_base_residual_count": base_report["base_residual_count"],
        "canonical59_remaining_residual_count": base_report["remaining_residual_count"],
        "canonical59_accepted_parents": sorted(x["label"] for x in base_report["accepted"]),
        "raw59_retained": base_report["raw59_retained"],
        "raw122_parent_table": "1RB---_1RC---_0RD---_1LD1RE_---0LF_------",
        "raw122_core_dependencies": raw122_dependencies,
        "raw122_source_ref": args.raw122_source_ref,
        "raw122_base_source_sha256": current_sha,
        "raw122_base_olean_sha256": sha(linked / "Raw122Base.olean"),
        "membership_source_sha256": sha(membership_source),
        "membership_olean_sha256": sha(membership_output),
        "membership_count": 1,
        "axioms": profiles,
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True
        ).strip(),
        "lean_version": subprocess.check_output(
            ["lean", "--version"], cwd=REPO_ROOT, text=True
        ).strip(),
    }
    (generated / "Raw122Canonical59Membership.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    (generated / "README.md").write_text(
        "# Raw122 exact membership in Canonical59\n\n"
        "Lean source compilation proves that the Raw122 parent table occurs exactly once "
        "in the accepted 59-residual Canonical59 roster. This is a membership result only; "
        "it does not establish the Raw122 parent Cover or any universal BB(6) upper bound.\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
