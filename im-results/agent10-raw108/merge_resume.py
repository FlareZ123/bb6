#!/usr/bin/env python3
"""Assemble resumed Raw108 shards without recompiling unchanged accepted Lean modules.

Historical generator inputs are checked against their original Git commit,
not against a later generator. The existing strict merge still checks current
tracked Lean source, every generated source and object hash, shared module
identities, compiler identity and the dependency graph. The final closure
compiler independently checks all module identities again.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "agent4-raw109"))
from merge_shards import merge, digest, require, inside

OLD_RUN = "45699436782"
OLD_REV = "68ab7dcfd6337c815ea61fed602f480ea95409e8"
OLD_GROUPS = {"cut", "small", "lf1", "le1", "lf0"}


def checked_provenance(repo, manifest, rev):
    """Check every tracked input against the exact source revision."""
    current = []
    for item in manifest["provenance_inputs"]:
        path = item["path"]
        src = inside(repo, path)
        old_bytes = subprocess.check_output(
            ["git", "show", f"{rev}:{path}"], cwd=repo
        )
        require(hashlib.sha256(old_bytes).hexdigest() == item["sha256"],
                f"{rev}: historical input hash mismatch {path}")
        if src.is_file() and digest(src) == item["sha256"]:
            current.append(item)
    return current


def resume(repo, downloads, output, config, run_id):
    groups = {name: set(modules) for name, modules in config["groups"].items()}
    prefix = config["artifact_prefix"]
    current_rev = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
    ).strip()
    require(set(x.name for x in downloads.iterdir()) ==
            {f"{prefix}-{g}" for g in groups}, "unexpected downloaded shard set")
    historical = []
    with tempfile.TemporaryDirectory(dir=downloads.parent) as tmp:
        stage = Path(tmp)
        for group in groups:
            artifact = f"{prefix}-{group}"
            source = downloads / artifact
            raw = (source / "manifest.json").read_bytes()
            manifest = json.loads(raw)
            old = group in OLD_GROUPS
            rev = OLD_REV if old else current_rev
            expected_run = OLD_RUN if old else run_id
            require(manifest["proof_source_revision"] == rev, f"{group}: source revision mismatch")
            require(str(manifest["workflow"]["run_id"]) == expected_run,
                    f"{group}: workflow run mismatch")
            # Preserve the original manifest and its hash, including all input
            # hashes even when later generators differ.
            current_inputs = checked_provenance(repo, manifest, rev)
            historical.append((group, raw, {
                "group": group,
                "source_revision": rev,
                "run_id": expected_run,
                "manifest_sha256": hashlib.sha256(raw).hexdigest(),
                "provenance_inputs": manifest["provenance_inputs"],
            }))
            staged = stage / artifact
            shutil.copytree(source, staged, copy_function=os.link)
            # Unlink the hard-linked manifest before creating the staged view.
            (staged / "manifest.json").unlink()
            manifest["provenance_inputs"] = current_inputs
            (staged / "manifest.json").write_text(json.dumps(manifest))
        merge(repo, stage, output, groups, prefix, allow_mixed_revisions=True)
    originals = output / "original-shard-manifests"
    originals.mkdir()
    for group, raw, info in historical:
        (originals / f"{group}.json").write_bytes(raw)
    manifest_path = output / "manifest.json"
    union = json.loads(manifest_path.read_text())
    union["historical_provenance"] = [info for _, _, info in historical]
    manifest_path.write_text(json.dumps(union, indent=2, sort_keys=True) + "\n")
    print(f"Retained {len(historical)} original manifests; all historical inputs matched their pinned revisions")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        raise SystemExit("usage: merge_resume.py DOWNLOADS OUTPUT CONFIG.json")
    resume(Path.cwd().resolve(), Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve(),
           json.loads(Path(sys.argv[3]).read_text()), os.environ["GITHUB_RUN_ID"])
