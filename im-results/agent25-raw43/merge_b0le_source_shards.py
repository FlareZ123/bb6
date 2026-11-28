#!/usr/bin/env python3
"""Strictly merge dependency-closed Lean proof shards for one Raw43 B0LE child.

Each shard is produced from the same workflow revision and compiler.  The
merged manifest is suitable as --precompiled-manifest input to
tools/lean_compile_closure.py.  The final source audit still recompiles the
generated child data/tree modules; only the expensive independent BiDFA batch
modules and their shared dependencies are reused.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil


def sha256(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--shards-root", type=Path, required=True)
    ap.add_argument("--generated-dir", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--variant", required=True)
    ap.add_argument("--revision", required=True)
    ap.add_argument("--expected-shards", type=int, default=4)
    args = ap.parse_args()

    if args.expected_shards < 2:
        raise ValueError("expected-shards must be at least 2")
    if not args.revision or len(args.revision) != 40:
        raise ValueError("revision must be a full 40-character Git SHA")

    batch_sources = sorted(args.generated_dir.glob("Raw43*BiDFABatch*.lean"))
    if not batch_sources:
        raise RuntimeError(f"no generated BiDFA batch sources under {args.generated_dir}")
    expected_batches = {path.stem for path in batch_sources}

    args.out.mkdir(parents=True, exist_ok=False)
    entries: dict[str, dict] = {}
    roots_seen: set[str] = set()
    base: dict | None = None

    for shard in range(args.expected_shards):
        directory = args.shards_root / f"raw43-b0le-shard-{shard}"
        expected_shard_roots = {
            path.stem for pos, path in enumerate(batch_sources)
            if pos % args.expected_shards == shard
        }
        manifest_path = directory / "manifest.json"
        if not expected_shard_roots:
            empty_marker = directory / "EMPTY"
            if not empty_marker.is_file():
                raise FileNotFoundError(
                    f"missing explicit empty-shard marker for shard {shard}: {empty_marker}"
                )
            if manifest_path.exists():
                raise ValueError(f"unexpected manifest for empty shard {shard}")
            print(f"Accepted explicit empty shard {shard}/{args.expected_shards}", flush=True)
            continue
        if not manifest_path.is_file():
            raise FileNotFoundError(f"missing shard manifest: {manifest_path}")
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if manifest.get("schema_version") != 1:
            raise ValueError(f"unsupported manifest schema in shard {shard}")
        if manifest.get("proof_source_revision") != args.revision:
            raise ValueError(
                f"shard {shard} proof revision {manifest.get('proof_source_revision')} "
                f"!= expected {args.revision}"
            )
        workflow = manifest.get("workflow", {})
        if workflow.get("workflow_head_sha") != args.revision:
            raise ValueError(f"shard {shard} workflow head does not match revision")
        expected_artifact = f"raw43-b0le-shard-{shard}"
        if manifest.get("artifact_name") != expected_artifact:
            raise ValueError(
                f"shard {shard} artifact {manifest.get('artifact_name')!r} "
                f"!= {expected_artifact!r}"
            )
        expected_label = f"raw43-{args.variant}-shard-{shard}"
        if manifest.get("label") != expected_label:
            raise ValueError(
                f"shard {shard} label {manifest.get('label')!r} != {expected_label!r}"
            )
        if base is None:
            base = manifest
        else:
            if manifest.get("lean_version") != base.get("lean_version"):
                raise ValueError(f"Lean version mismatch in shard {shard}")
            if manifest.get("lean_binary", {}).get("sha256") != base.get("lean_binary", {}).get("sha256"):
                raise ValueError(f"Lean compiler mismatch in shard {shard}")

        shard_roots = {entry["module"] for entry in manifest.get("roots", [])}
        if shard_roots != expected_shard_roots:
            missing = sorted(expected_shard_roots - shard_roots)
            extra = sorted(shard_roots - expected_shard_roots)
            raise ValueError(
                f"shard {shard} root assignment mismatch: missing={missing}, extra={extra}"
            )
        unknown_roots = shard_roots - expected_batches
        if unknown_roots:
            raise ValueError(f"shard {shard} has non-BiDFA roots: {sorted(unknown_roots)}")
        duplicate_roots = roots_seen & shard_roots
        if duplicate_roots:
            raise ValueError(f"duplicate BiDFA roots across shards: {sorted(duplicate_roots)}")
        roots_seen |= shard_roots

        for entry in manifest.get("modules", []):
            module = entry["module"]
            rel = Path(entry["olean_path"])
            if rel.is_absolute() or ".." in rel.parts:
                raise ValueError(f"unsafe olean path for {module}: {rel}")
            obj = directory / rel
            if not obj.is_file():
                raise FileNotFoundError(f"missing shard object for {module}: {obj}")
            if sha256(obj) != entry["olean_sha256"]:
                raise ValueError(f"olean SHA mismatch for {module} in shard {shard}")
            if module in entries:
                if entries[module]["module_identity_sha256"] != entry["module_identity_sha256"]:
                    raise ValueError(f"module identity conflict for {module}")
                continue
            entries[module] = entry
            target = args.out / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(obj, target)

    if roots_seen != expected_batches:
        missing = sorted(expected_batches - roots_seen)
        extra = sorted(roots_seen - expected_batches)
        raise ValueError(f"BiDFA shard coverage mismatch: missing={missing}, extra={extra}")
    if base is None:
        raise RuntimeError("no shard manifests were merged")

    merged = dict(
        base,
        label=f"raw43-{args.variant}-bidfa-union",
        source_revisions=[args.revision],
        claim={"theorem": None, "parent_table": None, "weighted_bound": None},
        artifact_name=None,
        roots=[],
        module_count=len(entries),
        modules=[entries[name] for name in sorted(entries)],
        provenance_inputs=[],
        precompiled_core=None,
    )
    (args.out / "manifest.json").write_text(
        json.dumps(merged, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        f"Merged {args.expected_shards} shards: {len(expected_batches)} BiDFA batch roots, "
        f"{len(entries)} dependency-closed modules",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
