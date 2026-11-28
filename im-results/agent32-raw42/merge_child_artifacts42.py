#!/usr/bin/env python3
"""Strictly merge twelve source-checked Raw42 child closure artifacts.

Shared module identities, source bytes, Lean compiler identity, and object bytes
must agree exactly. Mixed source revisions are recorded but never used to waive
a module/object conflict.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path

EXPECTED = {
    "0LA": (100006, "BB6.Agent32Raw420LA.Closed.cover"),
    "0RA": (1006,   "BB6.Agent32Raw420RA.Closed.cover"),
    "1LA": (100006, "BB6.Agent32Raw421LA.Closed.cover"),
    "1RA": (100006, "BB6.Agent32Raw421RA.Closed.cover"),
    "0RB": (1006,   "BB6.Agent32Raw420RB.Closed.cover"),
    "1LB": (100006, "BB6.Agent32Raw421LB.Closed.cover"),
    "1RB": (100006, "BB6.Agent32Raw421RB.Closed.cover"),
    "1LC": (100006, "BB6.Agent32Raw421LC.Closed.cover"),
    "0LE": (100006, "BB6.Agent32Raw420LE.Closed.cover"),
    "0RE": (100006, "BB6.Agent32Raw420RE.Closed.cover"),
    "1LE": (100006, "BB6.Agent32Raw421LE.Closed.cover"),
    "1RE": (100006, "BB6.Agent32Raw421RE.Closed.cover"),
}

IDENTITY_FIELDS = (
    "source_kind", "source_path", "source_sha256", "project_imports",
    "olean_path", "olean_sha256", "import_closure_sha256",
    "module_identity_sha256",
)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def copy_identical(src: Path, dst: Path, expected: str | None = None) -> None:
    if not src.is_file():
        raise FileNotFoundError(src)
    actual = digest(src)
    if expected is not None and actual != expected:
        raise RuntimeError(f"SHA-256 mismatch for {src}: {actual} != {expected}")
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        prior = digest(dst)
        if prior != actual:
            raise RuntimeError(f"content collision at {dst}: {prior} != {actual}")
    else:
        shutil.copy2(src, dst)


def one_manifest(child_dir: Path) -> Path:
    found = sorted(child_dir.rglob("manifest.json"))
    if len(found) != 1:
        raise RuntimeError(f"{child_dir}: expected one manifest.json, got {found}")
    return found[0]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--artifacts-root", required=True)
    ap.add_argument("--sources-out", required=True)
    ap.add_argument("--objects-out", required=True)
    ap.add_argument("--manifest-out", required=True)
    a = ap.parse_args()

    root = Path(a.artifacts_root)
    sources = Path(a.sources_out)
    objects = Path(a.objects_out)
    manifest_out = Path(a.manifest_out)
    shutil.rmtree(sources, ignore_errors=True)
    shutil.rmtree(objects, ignore_errors=True)
    sources.mkdir(parents=True)
    objects.mkdir(parents=True)

    base = None
    modules: dict[str, dict] = {}
    roots: dict[str, dict] = {}
    revisions: set[str] = set()
    children = []

    for child, (bound, theorem) in EXPECTED.items():
        child_dir = root / child
        manifest_path = one_manifest(child_dir)
        artifact_dir = manifest_path.parent
        m = json.loads(manifest_path.read_text())
        if m.get("schema_version") != 1:
            raise RuntimeError(f"{child}: unsupported manifest schema")
        claim = m.get("claim", {})
        if claim.get("weighted_bound") != bound:
            raise RuntimeError(f"{child}: wrong weighted bound {claim}")
        if claim.get("theorem") != theorem:
            raise RuntimeError(f"{child}: wrong theorem {claim}")

        if base is None:
            base = m
        else:
            if m.get("lean_version") != base.get("lean_version"):
                raise RuntimeError(f"{child}: Lean version differs")
            if m.get("lean_binary", {}).get("sha256") != base.get("lean_binary", {}).get("sha256"):
                raise RuntimeError(f"{child}: Lean binary differs")

        for rev in m.get("source_revisions", []):
            if rev:
                revisions.add(rev)
        for rev in (
            m.get("proof_source_revision"),
            m.get("workflow", {}).get("workflow_head_sha"),
        ):
            if rev:
                revisions.add(rev)

        for src in artifact_dir.rglob("*.lean"):
            rel = src.relative_to(artifact_dir)
            copy_identical(src, sources / rel)

        for entry in m.get("modules", []):
            mod = entry["module"]
            prior = modules.get(mod)
            if prior is not None:
                for field in IDENTITY_FIELDS:
                    if prior.get(field) != entry.get(field):
                        raise RuntimeError(
                            f"module identity conflict {mod}.{field}: "
                            f"{prior.get(field)!r} != {entry.get(field)!r}"
                        )
            else:
                modules[mod] = entry

            rel = Path(entry["olean_path"])
            if rel.is_absolute() or ".." in rel.parts:
                raise RuntimeError(f"{child}: unsafe object path {rel}")
            copy_identical(artifact_dir / rel, objects / rel, entry["olean_sha256"])

        for item in m.get("roots", []):
            mod = item["module"]
            if mod in roots and roots[mod] != item:
                raise RuntimeError(f"root identity conflict: {mod}")
            roots[mod] = item

        children.append({
            "child": child,
            "weighted_bound": bound,
            "theorem": theorem,
            "artifact_manifest_sha256": digest(manifest_path),
            "proof_source_revision": m.get("proof_source_revision"),
            "module_count": m.get("module_count"),
        })

    assert base is not None
    merged = dict(base)
    merged["label"] = "Raw42 twelve source-checked child closures"
    merged["proof_source_revision"] = os.environ.get(
        "GITHUB_SHA", base.get("proof_source_revision"))
    merged["source_revisions"] = sorted(revisions)
    merged["claim"] = {
        "theorem": "BB6.Agent17Raw42AcceptedParent.cover_global",
        "parent_table": "1RB---_1RC---_0RD---_1LD0LB_------_------",
        "weighted_bound": 6766859,
    }
    merged["artifact_name"] = "raw42-twelve-child-merged"
    merged["roots"] = [roots[k] for k in sorted(roots)]
    merged["modules"] = [modules[k] for k in sorted(modules)]
    merged["module_count"] = len(modules)
    merged["precompiled_core"] = None
    merged["merged_children"] = children
    merged["workflow"] = {
        "name": os.environ.get("GITHUB_WORKFLOW"),
        "run_id": os.environ.get("GITHUB_RUN_ID"),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "workflow_head_sha": os.environ.get("GITHUB_SHA"),
    }

    manifest_out.parent.mkdir(parents=True, exist_ok=True)
    manifest_out.write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n")
    print(
        f"[raw42-merge] children={len(children)} modules={len(modules)} "
        f"sources={sum(1 for _ in sources.rglob('*.lean'))} "
        f"objects={sum(1 for _ in objects.rglob('*.olean'))} "
        f"revisions={len(revisions)}",
        flush=True,
    )


if __name__ == "__main__":
    main()
