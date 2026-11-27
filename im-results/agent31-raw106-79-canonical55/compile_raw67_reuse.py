#!/usr/bin/env python3
"""Source-accept Raw67 by reusing exact Raw106 objects when source-identical.

The prior Raw67 hosted runs were terminated by the runner while compiling the
same large source closure that Raw106 had already accepted. This consumer pins
that Raw106 artifact, checks exact source hashes/import lists and compiler/base
identity, reuses only dependency-closed identical objects, and compiles every
remaining Raw67 module from source.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "im-results" / "agent16-canonical64-preflight"))
sys.path.insert(0, str(ROOT / "im-results" / "agent31-shared-core"))

import assemble_agent10_canonical64 as common
import assemble_canonical68 as a68

GEN = common.GEN
UNPACK_SCRIPT = common.UNPACK_SCRIPT
SOURCE_BLOBS = common.SOURCE_BLOBS
PARENTS = common.PARENTS
PARENT_THEOREMS = common.PARENT_THEOREMS
a63 = common.a63

RAW = "67"
REUSE_RUN = 45878084731
REUSE_REVISION = "75e7dcf16f98efda9ab3323b0acc16633833f180"
REUSE_ARTIFACT_ID = 15147725126
REUSE_ARTIFACT_NAME = "agent10-raw106-canonical64-parent-source-accepted"
REUSE_DIGEST = "1f4fbd81b26b300319e229eea0893e2d0998cb480704a237f61afef84db87b85"
REUSE_SIZE = 26661334


def download_raw106(work: Path, compiler_sha: str):
    run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{REUSE_RUN}")
    assert run["head_sha"] == REUSE_REVISION
    artifacts = a68.api_json(
        f"repos/{a68.REPO}/actions/runs/{REUSE_RUN}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["id"] == REUSE_ARTIFACT_ID]
    assert len(matches) == 1, matches
    item = matches[0]
    assert item["name"] == REUSE_ARTIFACT_NAME
    assert item["digest"] == "sha256:" + REUSE_DIGEST
    assert item["size_in_bytes"] == REUSE_SIZE
    assert not item["expired"]

    archive = work / "raw106.zip"
    with archive.open("wb") as out:
        subprocess.run(
            ["gh", "api", f"repos/{a68.REPO}/actions/artifacts/{REUSE_ARTIFACT_ID}/zip"],
            stdout=out, check=True,
        )
    assert common.sha(archive) == REUSE_DIGEST
    extracted = work / "raw106-artifact"
    extracted.mkdir()
    with zipfile.ZipFile(archive) as z:
        z.extractall(extracted)
    archive.unlink()

    report_paths = list(extracted.rglob("report.json"))
    reports = []
    for path in report_paths:
        try:
            report = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if str(report.get("raw")) == "106":
            reports.append((path, report))
    assert len(reports) == 1, [str(p) for p, _ in reports]
    report_path, report = reports[0]
    assert report["source_revision"] == REUSE_REVISION
    assert report["compiler_sha256"] == compiler_sha
    assert report["canonical64"]["artifact_id"] == a63.CANONICAL64_ARTIFACT
    assert report["canonical64"]["artifact_digest"] == "sha256:" + a63.CANONICAL64_DIGEST

    manifests = list(extracted.rglob("source-manifest.json"))
    candidates = []
    for path in manifests:
        try:
            manifest = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if manifest.get("root") == "Raw106Data":
            candidates.append((path, manifest))
    assert len(candidates) == 1, [str(p) for p, _ in candidates]
    manifest_path, manifest = candidates[0]
    assert manifest["proof_source_revision"] == REUSE_REVISION

    closure_candidates = [
        p for p in extracted.rglob("parent-olean-closure")
        if p.is_dir() and (p / "Raw106Data.olean").is_file()
    ]
    assert len(closure_candidates) == 1, [str(p) for p in closure_candidates]
    return closure_candidates[0], report_path, report, manifest_path, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler_sha = common.sha(prefix / "bin" / "lean")
    source_revision = common.git_revision(ROOT)

    subprocess.run([sys.executable, str(UNPACK_SCRIPT)], cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(GEN / "generate.py"), RAW], cwd=ROOT, check=True)

    index = common.module_index()
    source_root = work / "source-67"
    manifest, manifest_path = common.export_root(RAW, source_root, index, source_revision)
    assert manifest["root"] == "Raw67Data"

    source_map = {}
    for entry in manifest["modules"]:
        module = entry["module"]
        path = source_root / entry["bundle_path"]
        assert common.sha(path) == entry["source_sha256"]
        source_map[module] = {
            "path": path,
            "deps": list(entry["project_imports"]),
            "source_sha256": entry["source_sha256"],
            "source_path": entry["source_path"],
        }

    proof_files = ["Raw67Attainment.lean", "Raw67ParentCover.lean"]
    for name in proof_files:
        path = GEN / name
        assert common.git_blob(path) == SOURCE_BLOBS[name]
        source_map[path.stem] = {
            "path": path,
            "deps": list(common.parse_imports(path)),
            "source_sha256": common.sha(path),
            "source_path": str(path.relative_to(ROOT)),
        }

    parts = a63.download_canonical64_parts(work)
    base = work / "canonical64-dependencies"
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"]],
        work, base, families=a63.canonical64_families(parts),
    )

    raw106_work = work / "raw106-reuse"
    raw106_work.mkdir()
    raw106_closure, raw106_report_path, raw106_report, raw106_manifest_path, raw106_manifest = (
        download_raw106(raw106_work, compiler_sha)
    )
    raw106_entries = {e["module"]: e for e in raw106_manifest["modules"]}

    parent_dir = work / "parent-olean-closure"
    logs_dir = work / "compile-logs"
    parent_dir.mkdir()
    logs_dir.mkdir()
    env = dict(os.environ, LEAN_PATH=f"{parent_dir}:{base}")

    compiled = {
        module for module in source_map if common.module_file(base, module).is_file()
    }
    reused_base_modules = sorted(compiled)

    source_identical = {}
    for module, entry in source_map.items():
        old = raw106_entries.get(module)
        if not old:
            continue
        old_obj = common.module_file(raw106_closure, module)
        if (
            old["source_sha256"] == entry["source_sha256"]
            and old["project_imports"] == entry["deps"]
            and old_obj.is_file()
        ):
            source_identical[module] = old_obj

    reused_raw106 = []
    changed = True
    while changed:
        changed = False
        for module in sorted(source_identical):
            if module in compiled:
                continue
            if all(
                dep in compiled or common.module_file(base, dep).is_file()
                for dep in source_map[module]["deps"]
            ):
                output = common.module_file(parent_dir, module)
                output.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source_identical[module], output)
                compiled.add(module)
                reused_raw106.append(module)
                changed = True

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
            raise RuntimeError(f"unresolved/cyclic imports: {unresolved}")
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

    assert common.module_file(parent_dir, "Raw67ParentCover").is_file()
    assert common.module_file(parent_dir, "Raw67Attainment").is_file()

    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        ("agent10-raw67-reused", [base, parent_dir],
         ["Raw67ParentCover", "Raw67Attainment"])
    ]
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"], [parent_dir]],
        work, linked, families=families,
    )

    linked_env = dict(os.environ, LEAN_PATH=str(linked))
    canonical64_output, canonical64_log, canonical64_axioms = (
        a63.compile_canonical64(linked, linked_env, work)
    )
    parent_log = "\n".join(compile_logs)
    theorem_names = [
        theorem for theorem in PARENT_THEOREMS if "Agent10Raw67" in theorem
    ]
    # Reused modules need not print their old profiles; the decisive Raw67
    # theorem layer is newly compiled and carries all transitive dependencies.
    parent_axioms = a68.gate(parent_log, theorem_names)

    output = work / "output"
    output.mkdir()
    shutil.copytree(parent_dir, output / "parent-olean-closure")
    shutil.copytree(source_root, output / "source-67")
    for name in proof_files:
        shutil.copy2(GEN / name, output / name)
    shutil.copy2(linked / "kernel-link-manifest.json", output / "kernel-link-manifest.json")
    shutil.copy2(work / "reachable-link-audit.json", output / "reachable-link-audit.json")
    shutil.copy2(canonical64_output, output / "Canonical64Raw120Integrated.olean")
    shutil.copy2(work / "canonical64.log", output / "canonical64.log")
    shutil.copytree(logs_dir, output / "compile-logs")
    shutil.copy2(raw106_report_path, output / "raw106-reuse-report.json")
    shutil.copy2(raw106_manifest_path, output / "raw106-reuse-source-manifest.json")

    report = {
        "status": (
            "source-accepted Raw67 parent Cover with exact source-identical "
            "Raw106 object reuse; no roster cut or global upper-bound claim"
        ),
        "raw": RAW,
        "source_revision": source_revision,
        "lean_version": lean_version,
        "compiler_sha256": compiler_sha,
        "canonical64": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "recompiled_olean_sha256": common.sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "raw106_reuse": {
            "run_id": REUSE_RUN,
            "artifact_id": REUSE_ARTIFACT_ID,
            "artifact_name": REUSE_ARTIFACT_NAME,
            "artifact_digest": "sha256:" + REUSE_DIGEST,
            "source_revision": REUSE_REVISION,
            "source_identical_candidate_count": len(source_identical),
            "reused_module_count": len(reused_raw106),
            "reused_modules": reused_raw106,
        },
        "parent": {
            **PARENTS[RAW],
            "cover_theorem": "BB6.Agent10Raw67.parent_cover",
            "exactness_theorem": "BB6.Agent10Raw67.exact_weighted_threshold",
            "source_files": {name: SOURCE_BLOBS[name] for name in proof_files},
            "source_export_manifest_sha256": common.sha(manifest_path),
            "source_export_module_count": len(manifest["modules"]),
            "axioms": parent_axioms,
        },
        "reused_canonical64_modules": reused_base_modules,
        "compiled_source_module_count": len(source_map) - len(reused_base_modules) - len(reused_raw106),
        "strict_link_audit_sha256": common.sha(work / "reachable-link-audit.json"),
        "kernel_link_manifest_sha256": common.sha(linked / "kernel-link-manifest.json"),
        "no_global_cut_claim": True,
    }
    (output / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
