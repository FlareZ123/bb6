#!/usr/bin/env python3
"""Strictly merge retained Raw112 cuts, compile missing branch aggregators, and prove the parent Cover."""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from configure_retry import build_config
from run_retry_shard import PROVENANCE_INPUTS

PARENT_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
PARENT_THEOREM = "BB6.Agent47Raw112.parent_cover"
REQUIRED_AXIOMS = [
    "BB6.Agent47Raw112.sound",
    "BB6.Agent47Raw112.residual_count",
    "BB6.Agent47Raw112.residuals_covered",
    "BB6.Agent47Raw112.parent_cover",
]


def run_compile(
    roots: list[str],
    workdir: Path,
    precompiled: Path,
    label: str,
    artifact_name: str,
    log_path: Path,
    theorem: str | None = None,
    weighted_bound: int | None = None,
) -> None:
    if workdir.exists():
        shutil.rmtree(workdir)
    workdir.mkdir(parents=True)
    cmd = [
        sys.executable,
        "-u",
        "tools/lean_compile_closure.py",
        *roots,
        "--workdir",
        str(workdir),
        "--jobs",
        "2",
        "--precompiled-dir",
        str(precompiled),
        "--precompiled-manifest",
        str(precompiled / "manifest.json"),
        "--manifest",
        str(workdir / "manifest.json"),
        "--label",
        label,
        "--artifact-name",
        artifact_name,
    ]
    if theorem:
        cmd.extend(["--theorem", theorem, "--parent-table", PARENT_TABLE])
    if weighted_bound is not None:
        cmd.extend(["--weighted-bound", str(weighted_bound)])
    for path in PROVENANCE_INPUTS:
        cmd.extend(["--provenance-input", path])
    with log_path.open("w", encoding="utf-8") as log:
        result = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode != 0:
        # This driver redirects compiler output into /tmp. Without printing the
        # actual diagnostic, failed CI runs hide the decisive first error and
        # consume repeated queued jobs for the same unknown issue.
        print(f"{label}: compiler failed (exit {result.returncode}); "
              f"last source-diagnostic lines:", file=sys.stderr, flush=True)
        for line in log_path.read_text(encoding="utf-8", errors="replace").splitlines()[-130:]:
            print(line, file=sys.stderr, flush=True)
        raise subprocess.CalledProcessError(result.returncode, cmd)


def verify_reuse(manifest_path: Path, expected_compiled: set[str], label: str,
                 precompiled_seed: Path | None = None) -> None:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    modules = {item["module"] for item in manifest["modules"]}
    missing = expected_compiled - modules
    if missing:
        raise ValueError(f"{label}: missing compiled modules {sorted(missing)}")
    core = manifest.get("precompiled_core") or {}
    reused = set(core.get("reused_modules", []))
    if precompiled_seed is None:
        # Branch aggregators have no new external dependencies: exactly the
        # named root modules should be compiled from original source.
        expected_reused = modules - expected_compiled
    else:
        # Raw112ClosedCover additionally imports Raw112SiblingNever and
        # ResidualCover, which are not 24-branch shard dependencies. Those
        # modules legitimately compile fresh from checked-in source; what
        # matters is that *every* already certified source-identical object in
        # the full 24-branch seed was actually reused unchanged.
        seed = json.loads((precompiled_seed / "manifest.json").read_text(encoding="utf-8"))
        expected_reused = modules & {item["module"] for item in seed["modules"]}
        if expected_compiled & reused:
            raise ValueError(f"{label}: a target proof root was not rebuilt")
    if reused != expected_reused:
        raise ValueError(
            f"{label}: unexpected rebuilt dependencies: "
            f"missing={sorted(expected_reused - reused)}, extra={sorted(reused - expected_reused)}"
        )
    if core.get("proof_source_revision") != manifest["proof_source_revision"]:
        raise ValueError(f"{label}: precompiled source revision mismatch")
    if core.get("lean_binary_sha256") != manifest["lean_binary"]["sha256"]:
        raise ValueError(f"{label}: precompiled compiler identity mismatch")
    print(f"{label}: reused all {len(expected_reused)} source-identical parent dependencies")



def stitch_precompiled_roots(union: Path, branch_work: Path, combined: Path) -> None:
    """Retain *all* accepted shard objects plus newly compiled branch roots.

    The branch-root closure contains only dependencies of its three roots. It is
    not a replacement for the full 24-branch shard union. Feeding just that
    closure to the parent compiler silently recompiles the omitted branches.
    This explicit, identity-checked union repairs that loss without weakening
    the source/hash/axiom gates in lean_compile_closure.py.
    """
    left = json.loads((union / "manifest.json").read_text(encoding="utf-8"))
    right = json.loads((branch_work / "manifest.json").read_text(encoding="utf-8"))
    for field in ("schema_version", "proof_source_revision", "lean_version"):
        if left.get(field) != right.get(field):
            raise ValueError(f"parent seed: incompatible {field}")
    if left["lean_binary"]["sha256"] != right["lean_binary"]["sha256"]:
        raise ValueError("parent seed: incompatible compiler binary")
    fields = (
        "module", "source_sha256", "project_imports", "olean_path",
        "olean_sha256", "import_closure_sha256", "module_identity_sha256",
    )
    entries = {item["module"]: item for item in left["modules"]}
    if len(entries) != left["module_count"]:
        raise ValueError("parent seed: duplicate module in shard union")
    additions = []
    for item in right["modules"]:
        name = item["module"]
        if name in entries:
            if any(entries[name].get(k) != item.get(k) for k in fields):
                raise ValueError(f"parent seed: conflicting proof-object identity {name}")
        else:
            entries[name] = item
            additions.append(item)
    if len(set(item["module"] for item in right["modules"])) != right["module_count"]:
        raise ValueError("parent seed: duplicate branch-root module")
    for item in entries.values():
        if not set(item["project_imports"]) <= entries.keys():
            raise ValueError(f"parent seed: unclosed dependency of {item['module']}")
    if combined.exists():
        shutil.rmtree(combined)
    # All paths live under /tmp in the parent-only workflow. Hardlinks avoid
    # recopying a multi-GB certified archive; fallback is safe across devices.
    try:
        shutil.copytree(union, combined, copy_function=os.link)
    except OSError:
        if combined.exists():
            shutil.rmtree(combined)
        shutil.copytree(union, combined)
    for item in additions:
        rel = Path(item["olean_path"])
        if rel.is_absolute() or ".." in rel.parts:
            raise ValueError(f"parent seed: unsafe object path {rel}")
        target = combined / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        source = branch_work / rel
        if not source.is_file():
            raise FileNotFoundError(f"parent seed: missing branch object {source}")
        try:
            os.link(source, target)
        except OSError:
            shutil.copy2(source, target)
    roots = {item["module"]: item for item in left["roots"]}
    roots.update({item["module"]: item for item in right["roots"]})
    inputs = {item["path"]: item for item in left["provenance_inputs"]}
    for item in right["provenance_inputs"]:
        key = item["path"]
        if key in inputs and inputs[key] != item:
            raise ValueError(f"parent seed: conflicting provenance input {key}")
        inputs[key] = item
    left.update(
        label="raw112-shards-plus-branch-roots",
        artifact_name="raw112-parent-precompiled-seed",
        roots=[roots[key] for key in sorted(roots)],
        modules=[entries[key] for key in sorted(entries)],
        module_count=len(entries),
        provenance_inputs=[inputs[key] for key in sorted(inputs)],
        source_revisions=sorted(set(left.get("source_revisions", [])) |
                                set(right.get("source_revisions", []))),
        precompiled_core=None,
        precompiled_stitched_from=[
            {"label": "full-shard-union", "module_count": len(left["modules"])},
            {"label": "branch-aggregators", "module_count": len(right["modules"])},
        ],
    )
    (combined / "manifest.json").write_text(
        json.dumps(left, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"parent seed: retained {len(entries)} authenticated object modules; "
          f"added {len(additions)} branch-only modules")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--shards", type=Path, required=True)
    parser.add_argument("--union", type=Path, required=True)
    parser.add_argument("--branch-work", type=Path, required=True)
    parser.add_argument("--parent-work", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    source_run_id = os.environ.get("SOURCE_RUN_ID", "")
    prior_recovery_run_id = os.environ.get("PRIOR_RECOVERY_RUN_ID", "")
    if source_run_id != "45751911115" or prior_recovery_run_id != "45787320400":
        raise ValueError(
            f"unexpected pinned inputs: source={source_run_id}, prior={prior_recovery_run_id}"
        )

    root = args.root.resolve()
    shards = args.shards.resolve()
    union = args.union.resolve()
    branch_work = args.branch_work.resolve()
    parent_work = args.parent_work.resolve()
    output = args.output.resolve()

    patched_source = shards / "raw112-shard-r01a-deep" / "Raw112Kid01_01.lean"
    if not patched_source.is_file():
        raise FileNotFoundError(f"missing patched deep-root source: {patched_source}")
    shutil.copy2(patched_source, root / "Raw112Kid01_01.lean")

    config = build_config(root / "shard-config.json", "full")
    config_path = Path("/tmp/a47-raw112-full-config.json")
    config_path.write_text(json.dumps(config, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    for path in (union, branch_work, parent_work, output):
        if path.exists():
            shutil.rmtree(path)
    merge_cmd = [
        sys.executable,
        "im-results/agent4-raw109/merge_shards.py",
        str(shards),
        str(union),
        str(config_path),
    ]
    subprocess.run(merge_cmd, check=True)

    branch_log = Path("/tmp/a47-raw112-branch-roots.log")
    run_compile(
        [
            str(root / "Raw112Branch01.lean"),
            str(root / "Raw112Branch04.lean"),
            str(root / "Raw112Branch05.lean"),
        ],
        branch_work,
        union,
        "raw112-recovered-branch-aggregators",
        "raw112-recovered-branch-aggregators",
        branch_log,
    )
    verify_reuse(
        branch_work / "manifest.json",
        {"Raw112Branch01", "Raw112Branch04", "Raw112Branch05"},
        "branch aggregators",
    )

    # The three branch-root imports do not reach the other 21 accepted
    # branches. Preserve the complete shard union for the parent proof.
    seed = Path("/tmp/a47-raw112-parent-precompiled")
    stitch_precompiled_roots(union, branch_work, seed)
    parent_log = Path("/tmp/a47-raw112-parent-cover.log")
    run_compile(
        [str(root / "Raw112ClosedCover.lean")],
        parent_work,
        seed,
        "raw112-closed-parent-cover-targeted-retry",
        "raw112-closed-parent-cover",
        parent_log,
        theorem=PARENT_THEOREM,
        weighted_bound=100000,
    )
    verify_reuse(
        parent_work / "manifest.json",
        {"Raw112Data", "Raw112ClosedCover"},
        "parent Cover",
        precompiled_seed=seed,
    )
    subprocess.run(
        [
            sys.executable,
            "im-results/agent4-raw109/audit_axioms.py",
            str(parent_log),
            *REQUIRED_AXIOMS,
        ],
        check=True,
    )

    output.mkdir(parents=True)
    shutil.copytree(union, output / "union")
    shutil.copytree(branch_work, output / "branch-roots")
    shutil.copytree(parent_work, output / "parent")
    inputs = output / "inputs"
    inputs.mkdir()
    for name in (
        "Raw112Data.lean",
        "Raw112Branch01.lean",
        "Raw112Branch04.lean",
        "Raw112Branch05.lean",
        "Raw112Kid01_01.lean",
        "Raw112ClosedCover.lean",
        "Raw112Base.lean",
        "Raw112SiblingNever.lean",
        "unresolved.txt",
        "shard-config.json",
    ):
        source = root / name
        if source.is_file():
            shutil.copy2(source, inputs / name)
    shutil.copy2(branch_log, output / branch_log.name)
    shutil.copy2(parent_log, output / parent_log.name)

    summary = {
        "source_run_id": source_run_id,
        "prior_recovery_run_id": prior_recovery_run_id,
        "current_run_id": os.environ.get("GITHUB_RUN_ID"),
        "original_success_groups": ["0", "2", "3", "6", "7"],
        "prior_recovery_groups": [
            "r09", "r12", "r13", "r17", "r20", "r21", "r01b", "r05b", "r05c"
        ],
        "new_retry_groups": [
            "r01a-rest0", "r01a-rest1", "r01a-deep",
            "r04a", "r04b", "r04c", "r05a0", "r05a1"
        ],
        "full_union_root_modules": 93,
        "parent_table": PARENT_TABLE,
        "parent_theorem": PARENT_THEOREM,
        "weighted_bound": 100000,
        "maxRecDepth_for_Raw112Kid01_01": 300000,
    }
    (output / "retry-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("Raw112 full 24-branch union, branch aggregators, and parent Cover compiled and audited")


if __name__ == "__main__":
    main()
