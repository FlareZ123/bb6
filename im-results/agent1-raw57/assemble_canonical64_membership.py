#!/usr/bin/env python3
"""Source-audit Raw57's exact unique membership in the accepted Canonical64 roster.

This is a membership gate only. It does not remove Raw57, create a competing
roster, accept the Raw57 parent Cover, or claim a global BB(6) upper bound.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
SHARED = ROOT / "im-results" / "agent31-shared-core"
sys.path.insert(0, str(SHARED))
import assemble_canonical63 as a63  # noqa: E402

sys.path.insert(0, str(ROOT / "tools"))
from lean_compile_closure import (  # noqa: E402
    module_index,
    resolve_source,
    parse_imports,
    sha256_file,
    git_revision,
    display_source,
)

a68 = a63.a68
RAW57_DIR = ROOT / "im-results" / "agent1-raw57"
BRIDGE = RAW57_DIR / "Raw57ParentBridge.lean"
HELPER = RAW57_DIR / "Raw57Canonical64Membership.lean"

SOURCE_BLOBS = {
    "Raw57ParentBridge.lean": "ec63d2112dc1584ab2485876be35b31bfbdda86a",
    "Raw57Canonical64Membership.lean": "e3e0c0537f53fe7751a32e7f49d2000f0937c08c",
}
MEMBERSHIP_THEOREMS = [
    "BB6.Agent1Raw57Canonical64Membership.p57_root",
    "BB6.Agent1Raw57Canonical64Membership.p57_parent_count64",
    "BB6.Agent1Raw57Canonical64Membership.p57_index64",
]


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def git_blob(path):
    return subprocess.check_output(
        ["git", "hash-object", str(path)], cwd=ROOT, text=True
    ).strip()


def module_file(root, module):
    return root.joinpath(*module.split(".")).with_suffix(".olean")


def export_bridge_closure(out, index, revision):
    out.mkdir(parents=True, exist_ok=False)
    entries = {}

    def visit(module, path=None):
        if module in entries:
            return
        path = Path(path) if path else Path(resolve_source(module, index))
        deps = sorted(parse_imports(path))
        dst = out / (module.replace(".", "/") + ".lean")
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dst)
        entries[module] = {
            "module": module,
            "source_path": display_source(path),
            "bundle_path": str(dst.relative_to(out)),
            "source_sha256": sha256_file(path),
            "project_imports": deps,
        }
        for dep in deps:
            visit(dep)

    visit(BRIDGE.stem, BRIDGE)
    manifest = {
        "schema_version": 1,
        "kind": "source-only",
        "proof_source_revision": revision,
        "root": BRIDGE.stem,
        "modules": list(entries.values()),
    }
    manifest_path = out / "source-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version
    source_revision = git_revision(ROOT)

    for name, expected in SOURCE_BLOBS.items():
        path = RAW57_DIR / name
        actual = git_blob(path)
        assert actual == expected, (name, actual, expected)

    # Reconstruct any generated Lean sources before building the exact bridge closure.
    subprocess.run(
        [sys.executable, str(ROOT / "im-results" / "agent13-coverage" / "unpack.py")],
        cwd=ROOT,
        check=True,
    )
    index = module_index()
    source_dir = work / "raw57-parent-source"
    source_manifest = export_bridge_closure(source_dir, index, source_revision)
    source_map = {
        entry["module"]: {
            "path": source_dir / entry["bundle_path"],
            "deps": list(entry["project_imports"]),
            "source_sha256": entry["source_sha256"],
            "source_path": entry["source_path"],
        }
        for entry in source_manifest["modules"]
    }

    # Rebuild the pinned Canonical64 base, then compile Raw57ParentBridge against
    # that exact base so the membership theorem has one shared object identity.
    parts = a63.download_canonical64_parts(work)
    base = work / "canonical64-dependencies"
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"]],
        work,
        base,
        families=a63.canonical64_families(parts),
    )

    bridge_dir = work / "raw57-parent-closure"
    bridge_dir.mkdir()
    logs_dir = work / "compile-logs"
    logs_dir.mkdir()
    env = dict(os.environ, LEAN_PATH=f"{bridge_dir}:{base}")
    compiled = {
        module for module in source_map if module_file(base, module).is_file()
    }
    reused_base_modules = sorted(compiled)
    pending = set(source_map) - compiled
    compile_logs = []

    while pending:
        ready = sorted(
            module for module in pending
            if all(
                dep in compiled or module_file(base, dep).is_file()
                for dep in source_map[module]["deps"]
            )
        )
        if not ready:
            unresolved = {
                module: [
                    dep for dep in source_map[module]["deps"]
                    if dep not in compiled and not module_file(base, dep).is_file()
                ]
                for module in sorted(pending)
            }
            raise RuntimeError(f"Raw57 bridge source closure has unresolved/cyclic imports: {unresolved}")
        for module in ready:
            entry = source_map[module]
            output = module_file(bridge_dir, module)
            output.parent.mkdir(parents=True, exist_ok=True)
            log_path = logs_dir / (module.replace(".", "_") + ".log")
            log = a68.compile_module(entry["path"], output, env, log_path)
            if re.search(r"sorryAx|native_decide", log):
                raise AssertionError(f"forbidden proof mechanism in Raw57 bridge dependency {module}")
            compile_logs.append(log)
            compiled.add(module)
            pending.remove(module)

    assert (
        module_file(bridge_dir, "Raw57ParentBridge").is_file()
        or module_file(base, "Raw57ParentBridge").is_file()
    )

    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        ("raw57-parent-bridge", [bridge_dir], ["Raw57ParentBridge"])
    ]
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"], [bridge_dir]],
        work,
        linked,
        families=families,
    )

    linked_env = dict(os.environ, LEAN_PATH=str(linked))
    canonical64_output, canonical64_log, canonical64_axioms = (
        a63.compile_canonical64(linked, linked_env, work)
    )
    membership_output = linked / "Raw57Canonical64Membership.olean"
    membership_log = a68.compile_module(
        HELPER,
        membership_output,
        linked_env,
        work / "raw57-membership.log",
    )
    if re.search(r"sorryAx|native_decide", membership_log):
        raise AssertionError("forbidden proof mechanism in Raw57 Canonical64 membership")
    membership_axioms = a68.gate(membership_log, MEMBERSHIP_THEOREMS)

    output = work / "output"
    output.mkdir()
    for name in (
        "Canonical64Raw120Integrated.olean",
        "Raw57ParentBridge.olean",
        "Raw57Canonical64Membership.olean",
        "kernel-link-manifest.json",
    ):
        shutil.copy2(linked / name, output / name)
    shutil.copy2(work / "reachable-link-audit.json", output / "reachable-link-audit.json")
    shutil.copy2(work / "canonical64.log", output / "canonical64.log")
    shutil.copy2(work / "raw57-membership.log", output / "raw57-membership.log")
    shutil.copytree(source_dir, output / "raw57-parent-source")
    shutil.copytree(bridge_dir, output / "raw57-parent-olean-closure")
    shutil.copytree(logs_dir, output / "compile-logs")
    shutil.copy2(BRIDGE, output / BRIDGE.name)
    shutil.copy2(HELPER, output / HELPER.name)
    shutil.copy2(
        ROOT / "im-results" / "agent3-tnf-raw120" / "Canonical64Raw120Integrated.lean",
        output / "Canonical64Raw120Integrated.lean",
    )

    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    report = {
        "status": (
            "source-accepted exact unique Raw57 membership in the accepted Canonical64 "
            "roster; membership only, not a parent Cover or integrated roster cut"
        ),
        "membership_theorems": MEMBERSHIP_THEOREMS,
        "membership_count": 1,
        "zero_based_index": 33,
        "base_residual_count": 64,
        "no_parent_cover_claim": True,
        "no_global_cut_claim": True,
        "canonical64_base": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "artifact_name": a63.CANONICAL64_NAME,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "source_revision": a63.CANONICAL64_REVISION,
            "source_blob_sha": a63.CANONICAL64_SOURCE_BLOB_SHA,
            "recompiled_olean_sha256": sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "source_revision": source_revision,
        "source_blobs": SOURCE_BLOBS,
        "lean_version": lean_version,
        "compiler_sha256": sha(prefix / "bin" / "lean"),
        "raw57_bridge_source_module_count": len(source_manifest["modules"]),
        "raw57_bridge_source_manifest_sha256": sha(source_dir / "source-manifest.json"),
        "compiled_bridge_module_count": len(compiled) - len(reused_base_modules),
        "reused_canonical64_modules": reused_base_modules,
        "membership_axioms": membership_axioms,
        "strict_link_audit_sha256": sha(work / "reachable-link-audit.json"),
        "kernel_link_manifest_sha256": sha(linked / "kernel-link-manifest.json"),
    }
    (output / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print(
        "Raw57's exact unique membership in Canonical64 passed original-source "
        "compilation and strict source/olean-link and standard-axiom gates. "
        "No parent Cover or roster cut was made.",
        flush=True,
    )


if __name__ == "__main__":
    main()
