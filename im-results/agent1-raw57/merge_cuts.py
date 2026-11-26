#!/usr/bin/env python3
"""Strictly merge Raw57 proof-cut manifests and their reusable Lean objects."""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
GROUPS = ("early", "middle", "residual-a", "residual-b")
EXPECTED_ROOTS = {
    "early": {
        "Raw57RAData", "Raw57RB0Data", "Raw57RC0Data", "Raw57RB1Data",
        "Raw57RC1Data", "Raw57RE1Data", "Raw57RE0Data", "Raw57RF0Data",
        "Raw57ParentBridge",
    },
    "middle": {
        "Raw57LB0Data", "Raw57LC0Data", "Raw57LD0Data",
        "Raw57RA1Data", "Raw57RF1Data", "Raw57LC1Data",
    },
    "residual-a": {"Raw57LA1Data", "Raw57LB1Data", "Raw57LE1Data"},
    "residual-b": {"Raw57LF0Data", "Raw57LF1Data"},
}
IDENTITY_FIELDS = (
    "source_kind", "source_path", "source_sha256", "project_imports",
    "olean_path", "olean_sha256", "import_closure_sha256",
    "module_identity_sha256",
)

def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
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
            raise RuntimeError(f"content collision at {target}: {existing} != {actual}")
    else:
        shutil.copy2(source, target)

def safe_relative(value: str) -> Path:
    path = Path(value)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise RuntimeError(f"unsafe manifest path: {value}")
    return path

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

    base = None
    modules: dict[str, dict] = {}
    roots: dict[str, dict] = {}
    provenance: dict[str, str] = {}
    revisions: set[str] = set()
    group_records = []

    for group in GROUPS:
        directory = artifacts_root / group
        manifest_path = directory / "manifest.json"
        precompiled_dir = directory / "precompiled"
        if not manifest_path.is_file() or not precompiled_dir.is_dir():
            raise FileNotFoundError(f"incomplete Raw57 {group} artifact: {directory}")
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if manifest.get("schema_version") != 1:
            raise RuntimeError(f"unsupported manifest schema in {manifest_path}")
        if manifest.get("lean_version") is None or manifest.get("lean_binary", {}).get("sha256") is None:
            raise RuntimeError(f"missing Lean identity in {manifest_path}")
        if manifest.get("module_count") != len(manifest.get("modules", [])):
            raise RuntimeError(f"module count mismatch in {manifest_path}")
        if base is None:
            base = manifest
        else:
            checks = (
                ("lean_version", manifest.get("lean_version"), base.get("lean_version")),
                ("lean binary", manifest.get("lean_binary", {}).get("sha256"),
                 base.get("lean_binary", {}).get("sha256")),
                ("proof source revision", manifest.get("proof_source_revision"),
                 base.get("proof_source_revision")),
                ("workflow head SHA", manifest.get("workflow", {}).get("workflow_head_sha"),
                 base.get("workflow", {}).get("workflow_head_sha")),
            )
            for label, actual, expected in checks:
                if actual != expected:
                    raise RuntimeError(f"{label} differs across Raw57 cuts: {actual!r} != {expected!r}")

        group_roots = {item["module"] for item in manifest.get("roots", [])}
        if group_roots != EXPECTED_ROOTS[group]:
            raise RuntimeError(
                f"{group} root mismatch: expected {sorted(EXPECTED_ROOTS[group])}, "
                f"found {sorted(group_roots)}"
            )

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

            olean_path = safe_relative(entry["olean_path"])
            copy_identical(
                precompiled_dir / olean_path,
                precompiled_out / olean_path,
                entry["olean_sha256"],
            )

            source_path = safe_relative(entry["source_path"])
            if entry.get("source_kind") == "generated-or-untracked":
                module_path = Path(*module.split(".")).with_suffix(".lean")
                module_path = safe_relative(str(module_path))
                copy_identical(
                    precompiled_dir / module_path,
                    generated_out / module_path,
                    entry["source_sha256"],
                )
            else:
                tracked_source = REPO_ROOT / source_path
                if not tracked_source.is_file() or digest(tracked_source) != entry["source_sha256"]:
                    raise RuntimeError(f"tracked source mismatch for {module}: {tracked_source}")

        for item in manifest.get("roots", []):
            module = item["module"]
            if module in roots and roots[module] != item:
                raise RuntimeError(f"root identity conflict for {module}")
            roots[module] = item
        for item in manifest.get("provenance_inputs", []):
            path, sha = item["path"], item["sha256"]
            if path in provenance and provenance[path] != sha:
                raise RuntimeError(f"provenance input changed across cuts: {path}")
            provenance[path] = sha
        revisions.update(manifest.get("source_revisions", []))
        group_records.append({
            "group": group,
            "manifest_sha256": digest(manifest_path),
            "module_count": manifest["module_count"],
            "root_modules": sorted(group_roots),
        })

    if base is None:
        raise RuntimeError("no Raw57 cut manifests found")
    merged = dict(base)
    merged["label"] = "Raw57 parent reusable proof-cut union"
    merged["artifact_name"] = "raw57-parent-cuts-merged"
    merged["claim"] = None
    merged["roots"] = [roots[name] for name in sorted(roots)]
    merged["modules"] = [modules[name] for name in sorted(modules)]
    merged["module_count"] = len(modules)
    merged["provenance_inputs"] = [
        {"path": path, "sha256": provenance[path]} for path in sorted(provenance)
    ]
    merged["source_revisions"] = sorted(revisions)
    merged["precompiled_core"] = None
    merged["cut_manifests"] = group_records
    manifest_out.parent.mkdir(parents=True, exist_ok=True)
    manifest_out.write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"[raw57-cut-merge] groups={len(group_records)} roots={len(roots)} "
        f"modules={len(modules)} generated_sources={sum(1 for _ in generated_out.rglob('*.lean'))} "
        f"precompiled_oleans={sum(1 for _ in precompiled_out.rglob('*.olean'))}",
        flush=True,
    )

if __name__ == "__main__":
    main()
