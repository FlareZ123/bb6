#!/usr/bin/env python3
"""Compile one Agent10 Raw106/Raw79/Raw67 parent Cover against the pinned Canonical64 base.

Each parent is a separate CI job so a runner interruption cannot discard the
other parents' completed source closures. This stage proves only the named
parent Cover; unique Canonical64 membership is checked by the final assembler.
"""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

import assemble_agent10_canonical64 as common

ROOT = common.ROOT
GEN = common.GEN
UNPACK_SCRIPT = common.UNPACK_SCRIPT
SOURCE_BLOBS = common.SOURCE_BLOBS
PARENTS = common.PARENTS
PARENT_THEOREMS = common.PARENT_THEOREMS
a63 = common.a63
a68 = common.a68


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw", choices=("106", "79", "67"), required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    raw = args.raw
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version
    source_revision = common.git_revision(ROOT)

    subprocess.run([sys.executable, str(UNPACK_SCRIPT)], cwd=ROOT, check=True)
    subprocess.run(
        [sys.executable, str(GEN / "generate.py"), raw],
        cwd=ROOT,
        check=True,
    )

    index = common.module_index()
    source_root = work / f"source-{raw}"
    manifest, manifest_path = common.export_root(raw, source_root, index, source_revision)
    assert manifest["root"] == f"Raw{raw}Data"
    assert manifest["proof_source_revision"] == source_revision

    source_map = {}
    for entry in manifest["modules"]:
        module = entry["module"]
        path = source_root / entry["bundle_path"]
        assert common.sha(path) == entry["source_sha256"], (module, path)
        source_map[module] = {
            "path": path,
            "deps": list(entry["project_imports"]),
            "source_sha256": entry["source_sha256"],
            "source_path": entry["source_path"],
        }

    proof_files = [f"Raw{raw}Attainment.lean", f"Raw{raw}ParentCover.lean"]
    for name in proof_files:
        path = GEN / name
        expected = SOURCE_BLOBS[name]
        actual = common.git_blob(path)
        assert actual == expected, (name, actual, expected)
        module = path.stem
        candidate = {
            "path": path,
            "deps": list(common.parse_imports(path)),
            "source_sha256": common.sha(path),
            "source_path": str(path.relative_to(ROOT)),
        }
        old = source_map.get(module)
        if old and old["source_sha256"] != candidate["source_sha256"]:
            raise RuntimeError(f"proof source collides with generated module {module}")
        source_map[module] = candidate

    parts = a63.download_canonical64_parts(work)
    base = work / "canonical64-dependencies"
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"]],
        work,
        base,
        families=a63.canonical64_families(parts),
    )

    parent_dir = work / "parent-olean-closure"
    logs_dir = work / "compile-logs"
    parent_dir.mkdir()
    logs_dir.mkdir()
    env = dict(os.environ, LEAN_PATH=f"{parent_dir}:{base}")

    compiled = {
        module for module in source_map if common.module_file(base, module).is_file()
    }
    reused_base_modules = sorted(compiled)
    pending = set(source_map) - compiled
    compile_logs = []

    while pending:
        ready = sorted(
            module for module in pending
            if all(
                dep in compiled or common.module_file(base, dep).is_file()
                for dep in source_map[module]["deps"]
            )
        )
        if not ready:
            unresolved = {
                module: [
                    dep for dep in source_map[module]["deps"]
                    if dep not in compiled and not common.module_file(base, dep).is_file()
                ]
                for module in sorted(pending)
            }
            raise RuntimeError(f"source closure has unresolved/cyclic imports: {unresolved}")
        for module in ready:
            entry = source_map[module]
            output = common.module_file(parent_dir, module)
            output.parent.mkdir(parents=True, exist_ok=True)
            log_path = logs_dir / (module.replace(".", "_") + ".log")
            log = a68.compile_module(entry["path"], output, env, log_path)
            if re.search(r"sorryAx|native_decide", log):
                raise AssertionError(f"forbidden proof mechanism in {module}")
            compile_logs.append(log)
            compiled.add(module)
            pending.remove(module)

    for module in (f"Raw{raw}ParentCover", f"Raw{raw}Attainment"):
        assert common.module_file(parent_dir, module).is_file(), module

    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        (
            f"agent10-raw{raw}",
            [parent_dir],
            [f"Raw{raw}ParentCover", f"Raw{raw}Attainment"],
        )
    ]
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"], [parent_dir]],
        work,
        linked,
        families=families,
    )

    linked_env = dict(os.environ, LEAN_PATH=str(linked))
    canonical64_output, canonical64_log, canonical64_axioms = (
        a63.compile_canonical64(linked, linked_env, work)
    )
    parent_log = "\n".join(compile_logs)
    theorem_names = [
        theorem for theorem in PARENT_THEOREMS
        if f"Agent10Raw{raw}" in theorem
    ]
    parent_axioms = a68.gate(parent_log, theorem_names)

    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    output = work / "output"
    output.mkdir()
    shutil.copytree(parent_dir, output / "parent-olean-closure")
    shutil.copytree(source_root, output / f"source-{raw}")
    for name in proof_files:
        shutil.copy2(GEN / name, output / name)
    shutil.copy2(linked / "kernel-link-manifest.json", output / "kernel-link-manifest.json")
    shutil.copy2(work / "reachable-link-audit.json", output / "reachable-link-audit.json")
    shutil.copy2(canonical64_output, output / "Canonical64Raw120Integrated.olean")
    shutil.copy2(work / "canonical64.log", output / "canonical64.log")
    shutil.copytree(logs_dir, output / "compile-logs")

    report = {
        "status": (
            f"source-accepted Raw{raw} parent Cover against the pinned Canonical64 "
            "dependency base; no roster cut or global upper-bound claim"
        ),
        "raw": raw,
        "source_revision": source_revision,
        "lean_version": lean_version,
        "compiler_sha256": common.sha(prefix / "bin" / "lean"),
        "canonical64": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "artifact_name": a63.CANONICAL64_NAME,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "source_revision": a63.CANONICAL64_REVISION,
            "source_blob_sha": a63.CANONICAL64_SOURCE_BLOB_SHA,
            "recompiled_olean_sha256": common.sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "parent": {
            **PARENTS[raw],
            "cover_theorem": f"BB6.Agent10Raw{raw}.parent_cover",
            "exactness_theorem": f"BB6.Agent10Raw{raw}.exact_weighted_threshold",
            "source_files": {
                name: SOURCE_BLOBS[name] for name in proof_files
            },
            "source_export_manifest_sha256": common.sha(manifest_path),
            "source_export_module_count": len(manifest["modules"]),
            "axioms": parent_axioms,
        },
        "reused_canonical64_modules": reused_base_modules,
        "compiled_parent_source_module_count": len(compiled) - len(reused_base_modules),
        "strict_link_audit_sha256": common.sha(work / "reachable-link-audit.json"),
        "kernel_link_manifest_sha256": common.sha(linked / "kernel-link-manifest.json"),
        "no_global_cut_claim": True,
    }
    (output / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print(
        f"Raw{raw} parent Cover passed original-source compilation and strict "
        "Canonical64 dependency linking. Membership remains a separate gate.",
        flush=True,
    )


if __name__ == "__main__":
    main()
