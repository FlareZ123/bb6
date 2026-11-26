#!/usr/bin/env python3
"""Source-accept Agent10's Raw106/79/67 parent Covers and their Canonical64 membership.

The script regenerates the exact source closures, compiles them against the pinned
Canonical64 dependency base, strict-links the parent proof roots, and checks
unique membership. It does not remove roster entries or create a new global cut.
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
sys.path.insert(0, str(ROOT / "im-results" / "agent31-shared-core"))
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
GEN = ROOT / "im-results" / "agent10-tnf-multipump"
EXPORT_ROOT = ROOT / "im-results" / "agent16-canonical64-preflight"
EXPORT_SCRIPT = ROOT / "im-results" / "agent27-retained-parent-source" / "export.py"
UNPACK_SCRIPT = ROOT / "im-results" / "agent13-coverage" / "unpack.py"
HELPER = EXPORT_ROOT / "Agent10Canonical64Membership.lean"

SOURCE_BLOBS = {
    "Raw106Attainment.lean": "88264485637bb25e5914a0f86281afbbb45b231d",
    "Raw106ParentCover.lean": "620ff80fde0f53b592bcc7035a4f4e45c3554c7e",
    "Raw79Attainment.lean": "1803e64917da36d9b4c9f71d2b1a3a16b195f642",
    "Raw79ParentCover.lean": "3d3a4503b747f4786e588c9848dece2b4c2ba950",
    "Raw67Attainment.lean": "e2044fa3fee0475b7f87b84b7d321ad13b459568",
    "Raw67ParentCover.lean": "b8c1cb730e6416c09152ed9dc413d0574a2d40e2",
    "Agent10Canonical64Membership.lean": "6673a3dd7bb35e06bbb931b97a13f75f2be6afec",
}

PARENTS = {
    "106": {
        "bound": 253,
        "table": "1RB---_1RC1RF_0RD---_1LD1RE_---0LB_------",
    },
    "79": {
        "bound": 2354,
        "table": "1RB---_1RC1LE_0RD---_1LD1RE_---0LB_------",
    },
    "67": {
        "bound": 808,
        "table": "1RB---_1RC1LB_0RD---_1LD1RE_---0LB_------",
    },
}

MEMBERSHIP_THEOREMS = [
    "BB6.Agent16Agent10Canonical64Membership.p106_root",
    "BB6.Agent16Agent10Canonical64Membership.p79_root",
    "BB6.Agent16Agent10Canonical64Membership.p67_root",
    "BB6.Agent16Agent10Canonical64Membership.p106_parent_count64",
    "BB6.Agent16Agent10Canonical64Membership.p79_parent_count64",
    "BB6.Agent16Agent10Canonical64Membership.p67_parent_count64",
    "BB6.Agent16Agent10Canonical64Membership.p106_p79_distinct",
    "BB6.Agent16Agent10Canonical64Membership.p106_p67_distinct",
    "BB6.Agent16Agent10Canonical64Membership.p79_p67_distinct",
]

PARENT_THEOREMS = []
for raw in ("106", "79", "67"):
    ns = f"BB6.Agent10Raw{raw}"
    PARENT_THEOREMS.extend([
        f"{ns}.tree{raw}_checked",
        f"{ns}.all{raw}",
        f"{ns}.parent_eq_literal",
        f"{ns}.attainingCompatible",
        f"{ns}.attainingHalts",
        f"{ns}.attainingDelay",
        f"{ns}.parent_cover",
        f"{ns}.literal_cover",
        f"{ns}.exact_weighted_threshold",
    ])


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


def export_root(raw, out, index, revision):
    source = GEN / f"Raw{raw}Data.lean"
    if not source.is_file():
        raise FileNotFoundError(source)
    out.mkdir(parents=True, exist_ok=False)
    entries = {}

    def visit(module, path=None):
        if module in entries:
            return
        path = Path(path) if path else Path(resolve_source(module, index))
        deps = parse_imports(path)
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

    visit(source.stem, source)
    manifest = {
        "schema_version": 1,
        "kind": "source-only",
        "proof_source_revision": revision,
        "root": source.stem,
        "modules": list(entries.values()),
    }
    manifest_path = out / "source-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest, manifest_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version
    source_revision = git_revision(ROOT)

    # Regenerate all three retained parents in one pass; then export each
    # generated Data root and its exact project-import closure.
    subprocess.run([sys.executable, str(UNPACK_SCRIPT)], cwd=ROOT, check=True)
    subprocess.run(
        [sys.executable, str(GEN / "generate.py"), "106", "79", "67"],
        cwd=ROOT,
        check=True,
    )
    index = module_index()
    exports = {}
    source_map = {}

    for raw in ("106", "79", "67"):
        out = work / f"source-{raw}"
        manifest, manifest_path = export_root(raw, out, index, source_revision)
        assert manifest["root"] == f"Raw{raw}Data"
        assert manifest["proof_source_revision"] == source_revision
        exports[raw] = {
            "directory": out,
            "manifest": manifest,
            "manifest_path": manifest_path,
            "manifest_sha256": sha(manifest_path),
            "module_count": len(manifest["modules"]),
        }
        for entry in manifest["modules"]:
            module = entry["module"]
            path = out / entry["bundle_path"]
            assert sha256_file(path) == entry["source_sha256"], (module, path)
            candidate = {
                "path": path,
                "deps": list(entry["project_imports"]),
                "source_sha256": entry["source_sha256"],
                "source_path": entry["source_path"],
            }
            old = source_map.get(module)
            if old and (
                old["source_sha256"] != candidate["source_sha256"]
                or old["deps"] != candidate["deps"]
            ):
                raise RuntimeError(f"conflicting source exports for {module}: {old} vs {candidate}")
            source_map[module] = candidate

    proof_files = [
        "Raw106Attainment.lean", "Raw106ParentCover.lean",
        "Raw79Attainment.lean", "Raw79ParentCover.lean",
        "Raw67Attainment.lean", "Raw67ParentCover.lean",
    ]
    for name in proof_files:
        path = GEN / name
        expected = SOURCE_BLOBS[name]
        actual = git_blob(path)
        assert actual == expected, (name, actual, expected)
        module = path.stem
        candidate = {
            "path": path,
            "deps": list(parse_imports(path)),
            "source_sha256": sha(path),
            "source_path": str(path.relative_to(ROOT)),
        }
        old = source_map.get(module)
        if old and old["source_sha256"] != candidate["source_sha256"]:
            raise RuntimeError(f"proof source collides with generated module {module}")
        source_map[module] = candidate

    helper_expected = SOURCE_BLOBS["Agent10Canonical64Membership.lean"]
    assert git_blob(HELPER) == helper_expected, (git_blob(HELPER), helper_expected)

    parts = a63.download_canonical64_parts(work)
    base = work / "canonical64-dependencies"
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"]],
        work,
        base,
        families=a63.canonical64_families(parts),
    )

    parent_dir = work / "agent10-parent-closure"
    logs_dir = work / "compile-logs"
    parent_dir.mkdir()
    logs_dir.mkdir()
    env = dict(os.environ, LEAN_PATH=f"{parent_dir}:{base}")

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
            raise RuntimeError(f"source closure has unresolved/cyclic imports: {unresolved}")
        for module in ready:
            entry = source_map[module]
            output = module_file(parent_dir, module)
            output.parent.mkdir(parents=True, exist_ok=True)
            log_path = logs_dir / (module.replace(".", "_") + ".log")
            log = a68.compile_module(entry["path"], output, env, log_path)
            if re.search(r"sorryAx|native_decide", log):
                raise AssertionError(f"forbidden proof mechanism in {module}")
            compile_logs.append(log)
            compiled.add(module)
            pending.remove(module)

    for raw in ("106", "79", "67"):
        assert module_file(parent_dir, f"Raw{raw}ParentCover").is_file()
        assert module_file(parent_dir, f"Raw{raw}Attainment").is_file()

    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        (
            "agent10-parent-covers",
            [parent_dir],
            ["Raw106ParentCover", "Raw79ParentCover", "Raw67ParentCover"],
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
    membership_output = linked / "Agent10Canonical64Membership.olean"
    membership_log = a68.compile_module(
        HELPER, membership_output, linked_env, work / "agent10-membership.log"
    )
    if re.search(r"sorryAx|native_decide", membership_log):
        raise AssertionError("forbidden proof mechanism in membership helper")

    parent_log = "\n".join(compile_logs)
    parent_axioms = a68.gate(parent_log, PARENT_THEOREMS)
    membership_axioms = a68.gate(membership_log, MEMBERSHIP_THEOREMS)

    output = work / "output"
    output.mkdir()
    shutil.copytree(parent_dir, output / "parent-olean-closure")
    for raw in ("106", "79", "67"):
        shutil.copytree(exports[raw]["directory"], output / f"source-{raw}")
    for name in (
        "Canonical64Raw120Integrated.olean",
        "Agent10Canonical64Membership.olean",
        "kernel-link-manifest.json",
    ):
        shutil.copy2(linked / name, output / name)
    shutil.copy2(work / "reachable-link-audit.json", output / "reachable-link-audit.json")
    shutil.copy2(work / "canonical64.log", output / "canonical64.log")
    shutil.copy2(work / "agent10-membership.log", output / "agent10-membership.log")
    shutil.copytree(logs_dir, output / "compile-logs")
    for name in proof_files:
        shutil.copy2(GEN / name, output / name)
    shutil.copy2(HELPER, output / HELPER.name)
    shutil.copy2(
        ROOT / "im-results" / "agent3-tnf-raw120" / "Canonical64Raw120Integrated.lean",
        output / "Canonical64Raw120Integrated.lean",
    )

    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    report = {
        "status": (
            "source-accepted Raw106/79/67 exact parent Covers and unique Canonical64 "
            "membership; no roster cut or global upper bound"
        ),
        "source_revision": source_revision,
        "lean_version": lean_version,
        "compiler_sha256": sha(prefix / "bin" / "lean"),
        "canonical64": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "artifact_name": a63.CANONICAL64_NAME,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "source_revision": a63.CANONICAL64_REVISION,
            "source_blob_sha": a63.CANONICAL64_SOURCE_BLOB_SHA,
            "recompiled_olean_sha256": sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "parents": {
            raw: {
                **PARENTS[raw],
                "cover_theorem": f"BB6.Agent10Raw{raw}.parent_cover",
                "exactness_theorem": f"BB6.Agent10Raw{raw}.exact_weighted_threshold",
                "membership_theorem": (
                    f"BB6.Agent16Agent10Canonical64Membership.p{raw}_parent_count64"
                ),
                "membership_count": 1,
                "source_files": {
                    name: SOURCE_BLOBS[name]
                    for name in proof_files
                    if name.startswith(f"Raw{raw}")
                },
                "source_export_manifest_sha256": exports[raw]["manifest_sha256"],
                "source_export_module_count": exports[raw]["module_count"],
            }
            for raw in ("106", "79", "67")
        },
        "reused_canonical64_modules": reused_base_modules,
        "compiled_parent_source_module_count": len(compiled) - len(reused_base_modules),
        "parent_axioms": parent_axioms,
        "membership_axioms": membership_axioms,
        "strict_link_audit_sha256": sha(work / "reachable-link-audit.json"),
        "kernel_link_manifest_sha256": sha(linked / "kernel-link-manifest.json"),
        "no_global_cut_claim": True,
    }
    (output / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print(
        "Raw106/79/67 parent Covers and exact unique Canonical64 memberships "
        "passed original-source compilation and the strict link/axiom gates. "
        "No roster cut was made.",
        flush=True,
    )


if __name__ == "__main__":
    main()
