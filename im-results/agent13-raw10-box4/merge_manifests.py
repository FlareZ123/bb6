#!/usr/bin/env python3
"""Merge six source-checked Raw10 rectangle-4 slice artifacts without trusting collisions."""
from __future__ import annotations
import argparse
import hashlib
import json
import shutil
from pathlib import Path

EXPECTED = set(range(6, 12))
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
            raise RuntimeError(f"collision with different content: {target} ({existing} != {actual})")
    else:
        shutil.copy2(source, target)

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

    artifact_dirs = sorted(
        p for p in artifacts_root.glob("raw10-box4-slice-*") if p.is_dir()
    )
    found = {}
    for directory in artifact_dirs:
        try:
            slot = int(directory.name.rsplit("-", 1)[1])
        except ValueError as exc:
            raise RuntimeError(f"unexpected slice artifact name: {directory.name}") from exc
        if slot in found:
            raise RuntimeError(f"duplicate artifact for slice {slot}")
        found[slot] = directory
    if set(found) != EXPECTED:
        raise RuntimeError(f"expected slice artifacts {sorted(EXPECTED)}, found {sorted(found)}")

    shutil.rmtree(generated_out, ignore_errors=True)
    shutil.rmtree(precompiled_out, ignore_errors=True)
    generated_out.mkdir(parents=True, exist_ok=True)
    precompiled_out.mkdir(parents=True, exist_ok=True)

    base = None
    modules: dict[str, dict] = {}
    roots: dict[str, dict] = {}
    provenance: dict[str, str] = {}
    revisions = set()
    slice_manifests = []

    for slot in sorted(EXPECTED):
        directory = found[slot]
        manifest_path = directory / "manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if manifest.get("schema_version") != 1:
            raise RuntimeError(f"unsupported manifest schema in {manifest_path}")
        if manifest.get("claim", {}).get("weighted_bound") != 3640:
            raise RuntimeError(f"wrong weighted bound in slice {slot} manifest")
        if manifest.get("lean_version") is None or manifest.get("lean_binary", {}).get("sha256") is None:
            raise RuntimeError(f"missing Lean identity in slice {slot} manifest")
        if base is None:
            base = manifest
        else:
            if manifest["lean_version"] != base["lean_version"]:
                raise RuntimeError("Lean versions differ between slice artifacts")
            if manifest["lean_binary"]["sha256"] != base["lean_binary"]["sha256"]:
                raise RuntimeError("Lean compiler binary hashes differ between slice artifacts")
            if manifest["proof_source_revision"] != base["proof_source_revision"]:
                raise RuntimeError("source revisions differ between slice artifacts")
            if manifest.get("workflow", {}).get("workflow_head_sha") != base.get("workflow", {}).get("workflow_head_sha"):
                raise RuntimeError("workflow head SHAs differ between slice artifacts")
        revisions.add(manifest["proof_source_revision"])
        root_names = {item["module"] for item in manifest.get("roots", [])}
        if f"Box4Slice{slot}" not in root_names:
            raise RuntimeError(f"slice {slot} manifest does not certify Box4Slice{slot}")

        generated_dir = directory / "generated"
        if not generated_dir.is_dir():
            raise FileNotFoundError(generated_dir)
        for source in generated_dir.rglob("*"):
            if source.is_file():
                relative = source.relative_to(generated_dir)
                copy_identical(source, generated_out / relative)

        precompiled_dir = directory / "precompiled"
        if not precompiled_dir.is_dir():
            raise FileNotFoundError(precompiled_dir)
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
                raise RuntimeError(f"unsafe olean path for {module}: {relative}")
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
            path, sha = item["path"], item["sha256"]
            if path in provenance and provenance[path] != sha:
                raise RuntimeError(f"provenance input changed between slices: {path}")
            provenance[path] = sha
        slice_manifests.append({
            "slice": slot,
            "manifest_sha256": digest(manifest_path),
            "module_count": manifest.get("module_count"),
        })

    assert base is not None
    merged = dict(base)
    merged["label"] = "Raw10 rectangle 4 merged six-slice precompiled closure"
    merged["claim"] = {
        "theorem": "BB6.Agent13.Box4.sourceBound",
        "parent_table": "raw10Remainder[4]",
        "weighted_bound": 3640,
    }
    merged["artifact_name"] = "raw10-box4-slices-precompiled"
    merged["roots"] = [roots[k] for k in sorted(roots)]
    merged["modules"] = [modules[k] for k in sorted(modules)]
    merged["module_count"] = len(modules)
    merged["provenance_inputs"] = [
        {"path": k, "sha256": provenance[k]} for k in sorted(provenance)
    ]
    merged["source_revisions"] = sorted(revisions)
    merged["precompiled_core"] = None
    merged["slice_manifests"] = slice_manifests

    manifest_out.parent.mkdir(parents=True, exist_ok=True)
    manifest_out.write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"[box4-merge] slices={sorted(found)} modules={len(modules)} "
        f"roots={len(roots)} generated_files={sum(1 for _ in generated_out.rglob('*.lean'))} "
        f"precompiled_oleans={sum(1 for _ in precompiled_out.rglob('*.olean'))}",
        flush=True,
    )

if __name__ == "__main__":
    main()
