#!/usr/bin/env python3
"""Compile one bounded Raw112 retry cut against the retained partial union."""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

from raise_maxrecdepth import patch_file

PROVENANCE_INPUTS = [
    "im-results/agent47-raw112-cut/generate.py",
    "im-results/agent47-raw112-cut/symbolic.py",
    "im-results/agent47-raw112-cut/enumerate_fast.cpp",
    "im-results/agent47-raw112-cut/far-bank.txt",
    "im-results/agent47-raw112-cut/far-extra.txt",
    "im-results/agent47-raw112-cut/late.txt",
    "im-results/agent47-raw112-cut/ngram.txt",
    "im-results/agent47-raw112-cut/inductive-generators.tar.xz",
    "im-results/agent47-raw112-cut/Raw112Data.lean",
    "im-results/agent47-raw112-cut/unresolved.txt",
    "im-results/agent47-raw114-cut/seeded_far.cpp",
    "im-results/agent47-raw115-cut/counter.py",
    "im-results/agent47-raw114-cut/multi_sweep.py",
    "im-results/agent31-three-hole-tnf/generate_sweeps.py",
    "im-results/agent31-three-hole-tnf/generate_four_hole.py",
    "im-results/agent47-raw111-cut/ngram_sparse.cpp",
    "im-results/agent47-raw111-cut/emit_sparse.py",
    "im-results/agent13-coverage/BB6Coverage.lean.xz.b64",
    "im-results/agent13-coverage/unpack.py",
    "im-results/agent16-raw118/ResidualCover.lean",
    "tools/lean_compile_closure.py",
    "im-results/agent4-raw109/merge_shards.py",
    "im-results/agent4-raw109/audit_axioms.py",
    "im-results/agent47-raw112-cut/shard-config.json",
    "im-results/agent10-raw112-recovery/configure_retry.py",
    "im-results/agent10-raw112-recovery/raise_maxrecdepth.py",
    "im-results/agent10-raw112-recovery/run_retry_shard.py",
    "im-results/agent10-raw112-recovery/assemble_retry.py",
]


def roots_for(group: str) -> list[str]:
    if group == "r01a-rest0":
        return ["Raw112Kid01_00", *[f"Raw112Kid01_{i:02d}" for i in range(2, 6)]]
    if group == "r01a-rest1":
        return [f"Raw112Kid01_{i:02d}" for i in range(6, 12)]
    if group == "r01a-deep":
        return ["Raw112Kid01_01"]
    if group == "r04a":
        return [f"Raw112Kid04_{i:02d}" for i in range(0, 8)]
    if group == "r04b":
        return [f"Raw112Kid04_{i:02d}" for i in range(8, 16)]
    if group == "r04c":
        return [f"Raw112Kid04_{i:02d}" for i in range(16, 24)]
    if group == "r05a0":
        return [f"Raw112Kid05_{i:02d}" for i in range(0, 4)]
    if group == "r05a1":
        return [f"Raw112Kid05_{i:02d}" for i in range(4, 8)]
    raise ValueError(f"unknown retry group: {group}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--group", required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--workdir", type=Path, required=True)
    parser.add_argument("--precompiled-dir", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    work = args.workdir.resolve()
    precompiled = args.precompiled_dir.resolve()
    modules = roots_for(args.group)
    sources = [root / f"{module}.lean" for module in modules]
    for source in sources:
        if not source.is_file():
            raise FileNotFoundError(source)

    patch = None
    if args.group == "r01a-deep":
        patch = patch_file(root / "Raw112Kid01_01.lean", 300000)

    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    if patch is not None:
        shutil.copy2(root / "Raw112Kid01_01.lean", work / "Raw112Kid01_01.lean")

    cmd = [
        sys.executable,
        "-u",
        "tools/lean_compile_closure.py",
        *[str(source) for source in sources],
        "--workdir",
        str(work),
        "--jobs",
        "1",
        "--precompiled-dir",
        str(precompiled),
        "--precompiled-manifest",
        str(precompiled / "manifest.json"),
        "--manifest",
        str(work / "manifest.json"),
        "--label",
        f"raw112-targeted-retry-{args.group}",
        "--artifact-name",
        f"raw112-shard-{args.group}",
    ]
    for path in PROVENANCE_INPUTS:
        cmd.extend(["--provenance-input", path])
    subprocess.run(cmd, check=True)

    (work / "retry-group.json").write_text(
        json.dumps(
            {
                "group": args.group,
                "root_modules": modules,
                "maxRecDepth_patch": patch,
                "precompiled_manifest": str(precompiled / "manifest.json"),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"Raw112 retry group {args.group} accepted {len(modules)} root module(s)")


if __name__ == "__main__":
    main()
