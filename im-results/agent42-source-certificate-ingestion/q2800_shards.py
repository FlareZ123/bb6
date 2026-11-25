#!/usr/bin/env python3
"""Strict cross-run artifact ingestion for the five q2800 source-tree shards.

Each shard run compiles one theorem and records the exact source/object hashes
of its complete Coq dependency closure. The final consumer rebuilds that common
closure from the same pinned sources/compiler, rejects any mismatch, then
installs only the five independently compiled shard objects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
from pathlib import Path

SCHEMA = "bb6-q2800-shard-artifact-v1"
UPSTREAM_REPO = "ccz181078/busycoq"
UPSTREAM_REVISION = "33209bc7dc282b38c8cd6be507bfc551fea56108"
SHARDS = ("01", "02", "03", "04", "05")


def die(message: str) -> None:
    raise SystemExit(f"q2800 shard artifact error: {message}")


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read_manifest(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        die(f"cannot read {path}: {exc}")


def validate_common(manifest: dict, source_commit: str, coqc_version: str,
                    coqc_binary_sha256: str) -> None:
    expected = {
        "schema": SCHEMA,
        "source_commit": source_commit,
        "upstream_repo": UPSTREAM_REPO,
        "upstream_revision": UPSTREAM_REVISION,
        "coqc_version": coqc_version,
        "coqc_binary_sha256": coqc_binary_sha256,
    }
    for key, value in expected.items():
        if manifest.get(key) != value:
            die(f"{key} mismatch: artifact={manifest.get(key)!r}, expected={value!r}")


def pack(args: argparse.Namespace) -> None:
    verify_dir = Path(args.verify_dir).resolve()
    out_dir = Path(args.out_dir).resolve()
    shard = args.shard
    if shard not in SHARDS:
        die(f"invalid shard {shard!r}")
    if len(args.source_commit) != 40:
        die("source commit must be a full 40-character SHA")
    if args.upstream_revision != UPSTREAM_REVISION:
        die("unexpected upstream source revision")

    modules = []
    for obj in sorted(verify_dir.rglob("*.vo")):
        rel_obj = obj.relative_to(verify_dir).as_posix()
        src = obj.with_suffix(".v")
        if not src.is_file():
            die(f"compiled object has no matching source: {rel_obj}")
        rel_src = src.relative_to(verify_dir).as_posix()
        modules.append({
            "source_path": rel_src,
            "object_path": rel_obj,
            "source_sha256": digest(src),
            "object_sha256": digest(obj),
        })

    shard_source = f"Agent42Q2800BatchShard{shard}.v"
    shard_object = f"Agent42Q2800BatchShard{shard}.vo"
    by_source = {m["source_path"]: m for m in modules}
    if "Agent42Q2800BatchData.v" not in by_source:
        die("dependency closure does not contain Agent42Q2800BatchData.v")
    if shard_source not in by_source:
        die(f"dependency closure does not contain {shard_source}")
    shard_module_names = [
        m["source_path"] for m in modules
        if Path(m["source_path"]).name.startswith("Agent42Q2800BatchShard")
    ]
    if shard_module_names != [shard_source]:
        die(f"expected only {shard_source} in this shard build, found {shard_module_names}")

    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)
    shutil.copyfile(verify_dir / shard_source, out_dir / shard_source)
    shutil.copyfile(verify_dir / shard_object, out_dir / shard_object)

    manifest = {
        "schema": SCHEMA,
        "source_commit": args.source_commit,
        "upstream_repo": UPSTREAM_REPO,
        "upstream_revision": args.upstream_revision,
        "coqc_version": args.coqc_version,
        "coqc_binary_sha256": args.coqc_binary_sha256,
        "run_id": str(args.run_id),
        "shard": shard,
        "theorem": f"q2800_trees_shard{shard}_checked",
        "modules": modules,
    }
    (out_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"PACKED shard={shard} run={args.run_id} "
        f"closure_modules={len(modules)} "
        f"closure_sha256={hashlib.sha256(json.dumps(modules, sort_keys=True).encode()).hexdigest()}"
    )


def merge(args: argparse.Namespace) -> None:
    verify_dir = Path(args.verify_dir).resolve()
    artifacts_root = Path(args.artifacts_root).resolve()
    expected_runs = [part.strip() for part in args.expected_runs.split(",") if part.strip()]
    if len(expected_runs) != 5 or any(not x.isdigit() for x in expected_runs):
        die("--expected-runs must contain exactly five comma-separated numeric run IDs")

    manifests = {}
    module_maps = {}
    for shard, expected_run in zip(SHARDS, expected_runs):
        artifact_dir = artifacts_root / shard
        manifest = read_manifest(artifact_dir / "manifest.json")
        validate_common(
            manifest, args.source_commit, args.coqc_version,
            args.coqc_binary_sha256
        )
        if manifest.get("shard") != shard:
            die(f"artifact directory {shard} contains shard {manifest.get('shard')!r}")
        if str(manifest.get("run_id")) != expected_run:
            die(f"shard {shard} run ID {manifest.get('run_id')!r} != expected {expected_run!r}")
        if manifest.get("theorem") != f"q2800_trees_shard{shard}_checked":
            die(f"shard {shard} has an unexpected theorem name")

        entries = manifest.get("modules")
        if not isinstance(entries, list) or not entries:
            die(f"shard {shard} has no dependency manifest")
        module_map = {}
        for entry in entries:
            source_path = entry["source_path"]
            object_path = entry["object_path"]
            if source_path in module_map:
                die(f"duplicate module {source_path} in shard {shard}")
            local_source = verify_dir / source_path
            local_object = verify_dir / object_path
            if not local_source.is_file():
                die(f"assembly checkout is missing dependency source {source_path}")
            if digest(local_source) != entry["source_sha256"]:
                die(f"source hash mismatch for {source_path} in shard {shard}")
            module_map[source_path] = (
                object_path, entry["source_sha256"], entry["object_sha256"]
            )

        shard_source = f"Agent42Q2800BatchShard{shard}.v"
        shard_object = f"Agent42Q2800BatchShard{shard}.vo"
        own = module_map.get(shard_source)
        if own is None or own[0] != shard_object:
            die(f"shard {shard} manifest omits its own compiled theorem")
        artifact_source = artifact_dir / shard_source
        artifact_object = artifact_dir / shard_object
        if not artifact_source.is_file() or not artifact_object.is_file():
            die(f"shard {shard} artifact is missing its source/object pair")
        if digest(artifact_source) != own[1]:
            die(f"artifact source hash mismatch for shard {shard}")
        if digest(artifact_object) != own[2]:
            die(f"artifact object hash mismatch for shard {shard}")
        if digest(local_source := (verify_dir / shard_source)) != own[1]:
            die(f"current checkout source mismatch for shard {shard}")
        manifests[shard] = manifest
        module_maps[shard] = module_map

    # The five shard builds must have byte-identical source/object identities
    # for every shared dependency. A shared module name is never silently
    # resolved by copy order.
    common_maps = {}
    for shard in SHARDS:
        own_source = f"Agent42Q2800BatchShard{shard}.v"
        common_maps[shard] = {
            name: value for name, value in module_maps[shard].items()
            if name != own_source
        }
    baseline = common_maps["01"]
    for shard in SHARDS[1:]:
        if common_maps[shard] != baseline:
            keys = sorted(set(baseline) | set(common_maps[shard]))
            mismatch = next(
                (k for k in keys if baseline.get(k) != common_maps[shard].get(k)),
                "<unknown>"
            )
            die(f"shared dependency closure differs in shard {shard} at {mismatch}")

    # Recheck the common objects produced by the assembly job. This verifies
    # that imported shard objects were compiled against these exact objects.
    for source_path, (object_path, source_hash, object_hash) in baseline.items():
        local_source = verify_dir / source_path
        local_object = verify_dir / object_path
        if not local_object.is_file():
            die(f"assembly build did not produce common dependency object {object_path}")
        if digest(local_source) != source_hash or digest(local_object) != object_hash:
            die(f"assembly dependency identity mismatch for {source_path}")

    installed = []
    for shard in SHARDS:
        artifact_dir = artifacts_root / shard
        object_name = f"Agent42Q2800BatchShard{shard}.vo"
        destination = verify_dir / object_name
        shutil.copyfile(artifact_dir / object_name, destination)
        os.utime(destination, None)
        expected_hash = module_maps[shard][f"Agent42Q2800BatchShard{shard}.v"][2]
        if digest(destination) != expected_hash:
            die(f"installed object hash mismatch for shard {shard}")
        installed.append({
            "shard": shard,
            "run_id": manifests[shard]["run_id"],
            "theorem": manifests[shard]["theorem"],
            "source_sha256": module_maps[shard][f"Agent42Q2800BatchShard{shard}.v"][1],
            "object_sha256": expected_hash,
        })

    closure = [
        {"source_path": k, "object_path": v[0],
         "source_sha256": v[1], "object_sha256": v[2]}
        for k, v in sorted(baseline.items())
    ]
    merged = {
        "schema": SCHEMA + "-merged",
        "source_commit": args.source_commit,
        "upstream_repo": UPSTREAM_REPO,
        "upstream_revision": UPSTREAM_REVISION,
        "coqc_version": args.coqc_version,
        "coqc_binary_sha256": args.coqc_binary_sha256,
        "shared_dependency_count": len(closure),
        "shared_dependency_closure_sha256":
            hashlib.sha256(json.dumps(closure, sort_keys=True).encode()).hexdigest(),
        "shards": installed,
        "acceptance_boundary":
            "All five shard objects passed identity checks against a freshly rebuilt common dependency closure; the aggregate parent theorem and its assumption audit must still compile successfully.",
    }
    out = verify_dir / "q2800-shard-merged-manifest.json"
    out.write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"MERGED shards=5 shared_dependencies={len(closure)} "
        f"closure_sha256={merged['shared_dependency_closure_sha256']}"
    )
    print(f"MANIFEST {out}")


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("pack")
    p.add_argument("--verify-dir", required=True)
    p.add_argument("--out-dir", required=True)
    p.add_argument("--shard", required=True, choices=SHARDS)
    p.add_argument("--source-commit", required=True)
    p.add_argument("--upstream-revision", required=True)
    p.add_argument("--coqc-version", required=True)
    p.add_argument("--coqc-binary-sha256", required=True)
    p.add_argument("--run-id", required=True)
    p.set_defaults(func=pack)

    m = sub.add_parser("merge")
    m.add_argument("--verify-dir", required=True)
    m.add_argument("--artifacts-root", required=True)
    m.add_argument("--expected-runs", required=True)
    m.add_argument("--source-commit", required=True)
    m.add_argument("--coqc-version", required=True)
    m.add_argument("--coqc-binary-sha256", required=True)
    m.set_defaults(func=merge)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
