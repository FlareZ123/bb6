#!/usr/bin/env python3
"""Merge Raw122 parent closure shards with strict source/object identity checks."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys

STANDARD_PREFIXES = (
    "Lean", "Init", "Std", "Batteries", "Mathlib", "Cryptids", "BusyBeaver",
)
FIELDS = (
    "module", "source_path", "source_kind", "source_sha256",
    "project_imports", "olean_path", "olean_sha256",
    "import_closure_sha256", "module_identity_sha256",
)

def is_standard(module: str) -> bool:
    return any(module == p or module.startswith(p + ".") for p in STANDARD_PREFIXES)

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def compare(left: dict, right: dict, module: str) -> None:
    differences = [k for k in FIELDS if left.get(k) != right.get(k)]
    if differences:
        raise RuntimeError(
            f"conflicting source/object identity for {module}: {differences}"
        )

if len(sys.argv) != 4:
    raise SystemExit("usage: merge_parent_shards.py BASE_DIR SHARDS_DIR OUT_DIR")

base_dir, shards_dir, out_dir = map(Path, sys.argv[1:4])
base_path = base_dir / "manifest.json"
base = json.loads(base_path.read_text(encoding="utf-8"))
out_dir.mkdir(parents=True, exist_ok=True)

if base.get("schema_version") != 1:
    raise RuntimeError("unsupported base manifest schema")
base_modules = {x["module"]: x for x in base.get("modules", [])}
modules = dict(base_modules)
manifest_paths = sorted(shards_dir.rglob("manifest.json"))
if not manifest_paths:
    raise RuntimeError(f"no shard manifests under {shards_dir}")

manifest_bytes = [base_path.read_bytes()]
root_entries = list(base.get("roots", []))
provenance = {
    (x.get("path"), x.get("sha256")): x
    for x in base.get("provenance_inputs", [])
}
source_revisions = set(base.get("source_revisions", []))
if not source_revisions and base.get("proof_source_revision"):
    source_revisions.add(base["proof_source_revision"])

# The base artifact is copied once. Shard artifacts intentionally omit these
# objects, so every new object must be present in exactly one or more shards.
for item in base.get("modules", []):
    relative = Path(item["olean_path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise RuntimeError(f"unsafe base object path for {item['module']}: {relative}")
    source = base_dir / relative
    if not source.is_file():
        raise FileNotFoundError(source)
    actual = sha(source)
    if actual != item["olean_sha256"]:
        raise RuntimeError(f"base object hash mismatch for {item['module']}")
    destination = out_dir / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)

shard_summaries = []
for manifest_path in manifest_paths:
    shard_dir = manifest_path.parent
    shard = json.loads(manifest_path.read_text(encoding="utf-8"))
    if shard.get("schema_version") != base.get("schema_version"):
        raise RuntimeError(f"schema mismatch in {manifest_path}")
    if shard.get("lean_version") != base.get("lean_version"):
        raise RuntimeError(f"Lean version mismatch in {manifest_path}")
    if shard.get("lean_binary", {}).get("sha256") != base.get("lean_binary", {}).get("sha256"):
        raise RuntimeError(f"Lean compiler mismatch in {manifest_path}")

    manifest_bytes.append(manifest_path.read_bytes())
    for revision in shard.get("source_revisions", []):
        source_revisions.add(revision)
    if shard.get("proof_source_revision"):
        source_revisions.add(shard["proof_source_revision"])
    for root in shard.get("roots", []):
        key = (root.get("module"), root.get("source_sha256"))
        if not any((x.get("module"), x.get("source_sha256")) == key for x in root_entries):
            root_entries.append(root)
    for item in shard.get("provenance_inputs", []):
        key = (item.get("path"), item.get("sha256"))
        provenance[key] = item

    added = 0
    for item in shard.get("modules", []):
        module = item["module"]
        if module in modules:
            compare(modules[module], item, module)
            continue
        relative = Path(item["olean_path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise RuntimeError(f"unsafe shard object path for {module}: {relative}")
        source = shard_dir / relative
        if not source.is_file():
            raise FileNotFoundError(
                f"new object {module} missing from shard artifact {manifest_path}"
            )
        actual = sha(source)
        if actual != item["olean_sha256"]:
            raise RuntimeError(f"shard object hash mismatch for {module}")
        destination = out_dir / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            if sha(destination) != actual:
                raise RuntimeError(f"object conflict while merging {module}")
        else:
            shutil.copy2(source, destination)
        modules[module] = item
        added += 1

    shard_info_path = shard_dir / "shard.json"
    shard_info = json.loads(shard_info_path.read_text(encoding="utf-8")) if shard_info_path.is_file() else {}
    shard_summaries.append({
        "artifact": shard_dir.name,
        "manifest": str(manifest_path),
        "manifest_sha256": sha(manifest_path),
        "module_count": len(shard.get("modules", [])),
        "new_modules_added": added,
        "shard_id": shard_info.get("shard_id"),
        "root_path": shard_info.get("root_path"),
    })

# Verify exact object hashes and that the union is dependency-closed.
for module, item in modules.items():
    relative = Path(item["olean_path"])
    object_path = out_dir / relative
    if not object_path.is_file():
        raise FileNotFoundError(f"merged object missing for {module}: {object_path}")
    if sha(object_path) != item["olean_sha256"]:
        raise RuntimeError(f"merged object hash mismatch for {module}")
    for dependency in item.get("project_imports", []):
        if not is_standard(dependency) and dependency not in modules:
            raise RuntimeError(
                f"merged manifest is not dependency-closed: {module} imports {dependency}"
            )

merged = dict(base)
merged["label"] = "raw122-parent-sharded-precompiled-closure"
merged["artifact_name"] = "raw122-parent-sharded-precompiled"
merged["proof_source_revision"] = os.environ.get(
    "GITHUB_SHA", base.get("proof_source_revision")
)
merged["source_revisions"] = sorted(x for x in source_revisions if x)
merged["roots"] = sorted(root_entries, key=lambda x: (x.get("module", ""), x.get("source_path", "")))
merged["provenance_inputs"] = sorted(
    provenance.values(), key=lambda x: (x.get("path", ""), x.get("sha256", ""))
)
merged["modules"] = [modules[name] for name in sorted(modules)]
merged["module_count"] = len(modules)
merged["claim"] = {
    "theorem": "BB6.Agent43Raw122CompleteParent.parent_bound",
    "parent_table": "1RB---_1RC---_0RD---_1LD1RE_---0LF_------",
    "weighted_bound": 6766859,
}
merged["precompiled_core"] = {
    "source_revisions": merged["source_revisions"],
    "manifest_sha256": hashlib.sha256(b"".join(manifest_bytes)).hexdigest(),
    "reused_module_count": len(modules),
    "reused_modules": sorted(modules),
    "shards": shard_summaries,
}
merged_path = out_dir / "manifest.json"
merged_path.write_text(
    json.dumps(merged, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
(out_dir / "shards.json").write_text(
    json.dumps(shard_summaries, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
print(json.dumps({
    "base_modules": len(base_modules),
    "shard_count": len(shard_summaries),
    "merged_modules": len(modules),
    "new_modules": len(modules) - len(base_modules),
    "manifest": str(merged_path),
    "shards": shard_summaries,
}, indent=2), flush=True)
