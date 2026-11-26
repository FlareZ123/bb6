#!/usr/bin/env python3
"""Build exact partial/full Raw112 shard-union configurations for targeted recovery."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

ORIGINAL_GROUPS = ("0", "2", "3", "6", "7")

RECOVERY_GROUPS = {
    "r09": ["Raw112Branch09"],
    "r12": ["Raw112Branch12"],
    "r13": ["Raw112Branch13"],
    "r17": ["Raw112Branch17"],
    "r20": ["Raw112Branch20"],
    "r21": ["Raw112Branch21"],
    "r01b": [f"Raw112Kid01_{i:02d}" for i in range(12, 24)],
    "r05b": [f"Raw112Kid05_{i:02d}" for i in range(8, 16)],
    "r05c": [f"Raw112Kid05_{i:02d}" for i in range(16, 24)],
}

RETRY_GROUPS = {
    "r01a-rest0": ["Raw112Kid01_00", *[f"Raw112Kid01_{i:02d}" for i in range(2, 6)]],
    "r01a-rest1": [f"Raw112Kid01_{i:02d}" for i in range(6, 12)],
    "r01a-deep": ["Raw112Kid01_01"],
    "r04a": [f"Raw112Kid04_{i:02d}" for i in range(0, 8)],
    "r04b": [f"Raw112Kid04_{i:02d}" for i in range(8, 16)],
    "r04c": [f"Raw112Kid04_{i:02d}" for i in range(16, 24)],
    "r05a0": [f"Raw112Kid05_{i:02d}" for i in range(0, 4)],
    "r05a1": [f"Raw112Kid05_{i:02d}" for i in range(4, 8)],
}


def expected_roots(phase: str) -> set[str]:
    branches = {f"Raw112Branch{i:02d}" for i in range(24) if i not in (1, 4, 5)}
    if phase == "partial":
        kids = {
            *(f"Raw112Kid01_{i:02d}" for i in range(12, 24)),
            *(f"Raw112Kid05_{i:02d}" for i in range(8, 24)),
        }
    else:
        kids = {
            f"Raw112Kid{branch:02d}_{child:02d}"
            for branch in (1, 4, 5)
            for child in range(24)
        }
    return branches | kids


def build_config(source_config: Path, phase: str) -> dict:
    base = json.loads(source_config.read_text(encoding="utf-8"))
    source_groups = base["groups"]
    missing = set(ORIGINAL_GROUPS) - source_groups.keys()
    if missing:
        raise ValueError(f"original shard config lacks groups: {sorted(missing)}")

    groups = {name: list(source_groups[name]) for name in ORIGINAL_GROUPS}
    groups.update(RECOVERY_GROUPS)
    if phase == "full":
        groups.update(RETRY_GROUPS)
    elif phase != "partial":
        raise ValueError(f"unknown phase: {phase}")

    flat = [module for modules in groups.values() for module in modules]
    if len(flat) != len(set(flat)):
        raise ValueError("retry configuration contains duplicate root modules")
    expected = expected_roots(phase)
    if set(flat) != expected:
        raise ValueError(
            f"{phase} root coverage mismatch: missing={sorted(expected - set(flat))}, "
            f"extra={sorted(set(flat) - expected)}"
        )

    config = dict(base)
    config["artifact_prefix"] = "raw112-shard"
    config["allow_mixed_revisions"] = True
    config["groups"] = groups
    return config


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=("partial", "full"), required=True)
    parser.add_argument("--source-config", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    config = build_config(args.source_config, args.phase)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(config, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    roots = sum(len(modules) for modules in config["groups"].values())
    print(
        f"Raw112 {args.phase} config: {len(config['groups'])} artifact groups, "
        f"{roots} unique root modules; mixed revisions allowed only under strict identity checks"
    )


if __name__ == "__main__":
    main()
