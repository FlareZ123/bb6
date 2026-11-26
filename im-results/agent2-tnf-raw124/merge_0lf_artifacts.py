#!/usr/bin/env python3
"""Merge the eleven source-accepted Raw124 F1=0LF/F0 child closures.

The child artifacts were built by two existing manual targets.  Duplicate Lean
module identities and object bytes must agree exactly; source revisions may
differ, and are retained individually in the merged manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path

EXPECTED = {
    "0LE": (45827171994, "raw124-0lf-0LE-source-accepted", 2455,
            "BB6.Agent7Raw124ZeroLF0LE.bound_all", "a7"),
    "0RB": (45829435208, "raw124-0lf-0rb-source-accepted", 174,
            "BB6.Agent4Raw124ZeroLF0RB.bound_all", "a4"),
    "0RE": (45827051596, "raw124-0lf-0RE-source-accepted", 597,
            "BB6.Agent7Raw124ZeroLF0RE.bound_all", "a7"),
    "1LC": (45828605659, "raw124-0lf-1LC-source-accepted", 332,
            "BB6.Agent7Raw124ZeroLF1LC.bound_all", "a7"),
    "1RA": (45829497777, "raw124-0lf-1RA-source-accepted", 2931,
            "BB6.Agent7Raw124ZeroLF1RA.bound_all", "a7"),
    "1RE": (45828857309, "raw124-0lf-1RE-source-accepted", 271,
            "BB6.Agent7Raw124ZeroLF1RE.bound_all", "a7"),
    "0RA": (45832947347, "raw124-0lf-0RA-source-accepted", 430,
            "BB6.Agent7Raw124ZeroLF0RA.bound_all", "a7"),
    "1LA": (45834325697, "raw124-0lf-1LA-source-accepted", 1045,
            "BB6.Agent32Raw124ZeroLF1LA.bound_all", "a7"),
    "1LB": (45833222135, "raw124-0lf-1LB-source-accepted", 688,
            "BB6.Agent7Raw124ZeroLF1LB.bound_all", "a7"),
    "1LE": (45832599988, "raw124-0lf-1LE-source-accepted", 356,
            "BB6.Agent7Raw124ZeroLF1LE.bound_all", "a7"),
    "1RB": (45832956396, "raw124-0lf-1RB-source-accepted", 1088,
            "BB6.Agent7Raw124ZeroLF1RB.bound_all", "a7"),
}

IDENTITY_FIELDS = (
    "source_kind",
    "source_path",
    "source_sha256",
    "project_imports",
    "olean_path",
    "olean_sha256",
    "import_closure_sha256",
    "module_identity_sha256",
)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def copy_identical(source: Path, target: Path, expected_hash: str | None = None) -> None:
    if not source.is_file():
        raise FileNotFoundError(source)
    actual = digest(source)
    if expected_hash is not None and actual != expected_hash:
        raise RuntimeError(f"SHA-256 mismatch for {source}: {actual} != {expected_hash}")
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        existing = digest(target)
        if existing != actual:
            raise RuntimeError(
                f"collision with different content: {target} ({existing} != {actual})"
            )
    else:
        shutil.copy2(source, target)


def child_layout(directory: Path, layout: str) -> tuple[Path, Path, Path]:
    if layout == "a4":
        closure = directory / "a4-raw124-0lf-0rb-closure"
        return closure / "manifest.json", closure, directory / "a4-raw124-0lf-0rb-generated"
    return (
        directory / "a7-raw124.manifest.json",
        directory / "a7-raw124-closure",
        directory / "a7-raw124-generated",
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifacts-root", required=True)
    parser.add_argument("--generated-out", required=True)
    parser.add_argument("--precompiled-out", required=True)
    parser.add_argument("--manifest-out", required=True)
    args = parser.parse_args()

    artifacts_root = Path(args.artifacts_root)
    generated_out = Path(args.generated_out)
    precompiled_out = Path(args.precompiled_out)
    manifest_out = Path(args.manifest_out)

    shutil.rmtree(generated_out, ignore_errors=True)
    shutil.rmtree(precompiled_out, ignore_errors=True)
    generated_out.mkdir(parents=True, exist_ok=True)
    precompiled_out.mkdir(parents=True, exist_ok=True)

    base: dict | None = None
    modules: dict[str, dict] = {}
    roots: dict[str, dict] = {}
    provenance: set[tuple[str, str]] = set()
    revisions: set[str] = set()
    child_manifests: list[dict] = []

    for child, (run_id, artifact_name, bound, theorem, layout) in EXPECTED.items():
        directory = artifacts_root / child
        manifest_path, precompiled_dir, generated_dir = child_layout(directory, layout)
        if not directory.is_dir():
            raise FileNotFoundError(f"missing downloaded artifact directory: {directory}")
        if not manifest_path.is_file():
            raise FileNotFoundError(f"missing manifest for {child}: {manifest_path}")
        if not precompiled_dir.is_dir():
            raise FileNotFoundError(f"missing precompiled directory for {child}: {precompiled_dir}")
        if not generated_dir.is_dir():
            raise FileNotFoundError(f"missing generated source directory for {child}: {generated_dir}")

        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if manifest.get("schema_version") != 1:
            raise RuntimeError(f"unsupported manifest schema for {child}")
        if manifest.get("claim", {}).get("weighted_bound") != bound:
            raise RuntimeError(f"wrong weighted bound for {child}: {manifest.get('claim')}")
        if manifest.get("claim", {}).get("theorem") != theorem:
            raise RuntimeError(f"wrong theorem for {child}: {manifest.get('claim')}")
        if manifest.get("lean_version") is None or not manifest.get("lean_binary", {}).get("sha256"):
            raise RuntimeError(f"missing Lean identity for {child}")

        if base is None:
            base = manifest
        else:
            if manifest["lean_version"] != base["lean_version"]:
                raise RuntimeError(f"Lean versions differ at {child}")
            if manifest["lean_binary"]["sha256"] != base["lean_binary"]["sha256"]:
                raise RuntimeError(f"Lean compiler binary hashes differ at {child}")

        for revision in manifest.get("source_revisions", []):
            if revision:
                revisions.add(revision)
        if manifest.get("proof_source_revision"):
            revisions.add(manifest["proof_source_revision"])
        workflow_sha = manifest.get("workflow", {}).get("workflow_head_sha")
        if workflow_sha:
            revisions.add(workflow_sha)

        for source in generated_dir.rglob("*.lean"):
            if source.is_file():
                copy_identical(source, generated_out / source.relative_to(generated_dir))

        for entry in manifest.get("modules", []):
            module = entry["module"]
            previous = modules.get(module)
            if previous is not None:
                for field in IDENTITY_FIELDS:
                    if previous.get(field) != entry.get(field):
                        raise RuntimeError(
                            f"module identity conflict for {module}.{field}: "
                            f"{previous.get(field)!r} != {entry.get(field)!r}"
                        )
            else:
                modules[module] = entry

            relative = Path(entry["olean_path"])
            if relative.is_absolute() or ".." in relative.parts:
                raise RuntimeError(f"unsafe precompiled object path for {module}: {relative}")
            copy_identical(
                precompiled_dir / relative,
                precompiled_out / relative,
                entry["olean_sha256"],
            )

        for item in manifest.get("roots", []):
            module = item["module"]
            if module in roots and roots[module] != item:
                raise RuntimeError(f"root identity conflict for {module}")
            roots[module] = item

        for item in manifest.get("provenance_inputs", []):
            provenance.add((item["path"], item["sha256"]))
        provenance.add((f"actions-artifact:{artifact_name}:manifest", digest(manifest_path)))

        child_manifests.append({
            "child": child,
            "run_id": run_id,
            "artifact_name": artifact_name,
            "manifest_sha256": digest(manifest_path),
            "module_count": manifest.get("module_count"),
            "weighted_bound": bound,
            "theorem": theorem,
            "proof_source_revision": manifest.get("proof_source_revision"),
        })

    assert base is not None
    merged = dict(base)
    merged["label"] = "Raw124 F1=0LF parent frontier: eleven accepted F0 child Covers"
    merged["proof_source_revision"] = os.environ.get(
        "GITHUB_SHA", base.get("proof_source_revision")
    )
    merged["source_revisions"] = sorted(revisions)
    merged["workflow"] = {
        "name": os.environ.get("GITHUB_WORKFLOW"),
        "run_id": os.environ.get("GITHUB_RUN_ID"),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "workflow_head_sha": os.environ.get("GITHUB_SHA"),
    }
    merged["claim"] = {
        "theorem": "BB6.Agent2Raw124ZeroLFParentFrontier.parent_cut",
        "parent_table": "1RB---_1RC---_0RD---_1LD1RE_---1LF_0LF",
        "weighted_bound": None,
    }
    merged["artifact_name"] = "raw124-0lf-parent-frontier-precompiled"
    merged["roots"] = [roots[k] for k in sorted(roots)]
    merged["modules"] = [modules[k] for k in sorted(modules)]
    merged["module_count"] = len(modules)
    merged["provenance_inputs"] = [
        {"path": path, "sha256": sha} for path, sha in sorted(provenance)
    ]
    merged["precompiled_core"] = None
    merged["merged_children"] = child_manifests

    manifest_out.parent.mkdir(parents=True, exist_ok=True)
    manifest_out.write_text(
        json.dumps(merged, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"[raw124-0lf-merge] children={len(child_manifests)} modules={len(modules)} "
        f"roots={len(roots)} generated_files={sum(1 for _ in generated_out.rglob('*.lean'))} "
        f"precompiled_oleans={sum(1 for _ in precompiled_out.rglob('*.olean'))} "
        f"source_revisions={len(revisions)}",
        flush=True,
    )


if __name__ == "__main__":
    main()
