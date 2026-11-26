#!/usr/bin/env python3
"""Recreate the pinned source side of the Raw122 parent precompiled manifest."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path.cwd().resolve()
if len(sys.argv) != 2:
    raise SystemExit("usage: pin_parent_sources.py PREPIN_MANIFEST")
manifest_path = Path(sys.argv[1]).resolve()
source_ref = os.environ.get("SOURCE_REF")
if not source_ref:
    raise SystemExit("SOURCE_REF must name the original source revision")
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

subprocess.run(
    ["git", "fetch", "--no-tags", "--depth=1", "origin", source_ref],
    cwd=ROOT, check=True,
)

paths = set()
tracked = [m for m in manifest.get("modules", []) if m.get("source_kind") == "tracked"]
for item in tracked:
    source = Path(item["source_path"])
    if not source.is_absolute():
        source = ROOT / source
    try:
        relative = source.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        continue
    exists = subprocess.run(
        ["git", "cat-file", "-e", f"{source_ref}:{relative}"],
        cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    if exists.returncode == 0:
        paths.add(relative)

if paths:
    subprocess.run(
        ["git", "checkout", source_ref, "--", *sorted(paths)],
        cwd=ROOT, check=True,
    )

checked = 0
for item in tracked:
    source = Path(item["source_path"])
    if not source.is_absolute():
        source = ROOT / source
    source = source.resolve()
    if not source.is_file():
        raise FileNotFoundError(source)
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    if actual != item["source_sha256"]:
        raise RuntimeError(
            f"pinned source hash mismatch for {item['module']}: "
            f"{actual} != {item['source_sha256']} ({source})"
        )
    checked += 1

print(
    f"pinned and verified {checked} tracked source(s) from {source_ref}; "
    f"{len(paths)} paths were present at that revision",
    flush=True,
)
