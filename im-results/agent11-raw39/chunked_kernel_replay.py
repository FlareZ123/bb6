#!/usr/bin/env python3
"""Chunked, original-kernel replay of an accepted Lean proof import cone.

A conventional relocated import cone may contain thousands of modules. Calling
the Lean kernel once for EACH affected source module repeatedly loads the
ever-growing prior environment. This variant groups topologically consecutive
affected modules into bounded chunks: each chunk imports the preceding checked
chunk and its untouched base dependencies, then Lean.Replay checks all proof
constants in that chunk at trust level zero.

This is a certificate transport tool, not a proof by fiat. The caller must
authenticate the original source/object closure, the destination's closure,
and the actual exported axiom profile after replay.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

KERNEL_SLICE = Path(__file__).resolve().parent.parent / "agent32-raw59" / "kernel-slice"
sys.path.insert(0, str(KERNEL_SLICE))
from stage_relocate import relocate, sha, write_lines


def relocate_chunked(*, producer_files, base, work, root_module, root_names,
                     prefix, tool, comparator=None, comparator_batch=None,
                     allow_compatible=False, chunk_size=64, resume_from=None):
    if chunk_size < 1:
        raise ValueError("chunk_size must be >= 1")
    producer_files = [Path(x).resolve() for x in producer_files]
    base, work = Path(base).resolve(), Path(work).resolve()

    # Reuse the source-authenticated dependency and kernel-constant plan.
    # No affected object is imported or trusted in the destination yet.
    report, output, names = relocate(
        producer_files=producer_files, base=base, work=work,
        root_module=root_module, root_names=root_names,
        prefix=prefix, tool=tool, comparator=comparator,
        comparator_batch=comparator_batch, allow_compatible=allow_compatible,
        plan_only=True)

    if report.get('mode') == 'authenticated-original-compatible-link':
        return report, output, names

    index = {}
    for line in (work / "module-index.jsonl").read_text().splitlines():
        entry = json.loads(line)
        module = Path(entry["path"]).stem
        if module in index:
            raise ValueError("duplicate producer module " + module)
        index[module] = entry
    files = {p.stem: p for p in producer_files}
    if len(files) != len(producer_files):
        raise ValueError("duplicate producer object path/name")

    # DFS import postorder, exactly as in the original planner.
    seen, visiting, order = set(), set(), []
    def visit(module):
        if module in seen:
            return
        if module not in index:
            return
        if module in visiting:
            raise ValueError("cyclic import " + module)
        visiting.add(module)
        for dep in index[module]["imports"]:
            visit(dep)
        visiting.remove(module)
        seen.add(module)
        order.append(module)
    visit(root_module)

    affected_paths = [
        Path(x).resolve() for x in
        (work / "affected-objects.txt").read_text().splitlines() if x
    ]
    affected = {p.stem for p in affected_paths}
    if len(affected) != len(affected_paths) or not affected:
        raise ValueError("empty/duplicated affected cone; use strict linker")
    if not affected <= set(order):
        raise ValueError("affected modules outside target import cone")
    rank = {m: i for i, m in enumerate(order)}
    affected_order = sorted(affected, key=rank.__getitem__)

    # Unaffected producer modules may be imported unchanged, but NEVER
    # overwrite a prior accepted base object.
    copied = []
    for module in order:
        if module in affected:
            continue
        source, original = files[module], base / (module + ".olean")
        if not original.is_file():
            dest = output / source.name
            shutil.copy2(source, dest)
            copied.append(dest.name)

    sysroot = Path(subprocess.check_output(
        ["lean", "--print-prefix"], text=True).strip())
    env = dict(os.environ,
               LEAN_SYSROOT=str(sysroot),
               LEAN_PATH=os.pathsep.join([str(output), str(base)]))
    old_stage = None
    groups = []
    start_offset = 0
    if resume_from is not None:
        resume_from = Path(resume_from).resolve()
        prior_path = resume_from / "report.json"
        if not prior_path.is_file():
            raise FileNotFoundError("missing resumable replay report " + str(prior_path))
        prior = json.loads(prior_path.read_text())
        stable = (
            "root_module", "prefix", "root_names", "source_modules",
            "affected_modules", "selected_declarations", "collisions",
            "kernel_comparison",
        )
        for key in stable:
            if prior.get(key) != report.get(key):
                raise ValueError("resume plan mismatch at " + key)
        prior_groups = prior.get("chunks", [])
        if not isinstance(prior_groups, list):
            raise ValueError("resume chunks must be a list")
        max_groups = (len(affected_order) + chunk_size - 1) // chunk_size
        if len(prior_groups) > max_groups:
            raise ValueError("resume has more chunks than reconstructed plan")
        for chunk_no, prior_group in enumerate(prior_groups):
            offset = chunk_no * chunk_size
            expected_group = affected_order[offset:offset + chunk_size]
            stage = prefix + "Chunk" + format(chunk_no, "04d")
            if prior_group.get("stage") != stage:
                raise ValueError("resume stage mismatch at chunk " + str(chunk_no))
            if prior_group.get("module_count") != len(expected_group):
                raise ValueError("resume module count mismatch at " + stage)
            if prior_group.get("source_modules") != expected_group:
                raise ValueError("resume source-module mismatch at " + stage)
            source = resume_from / "objects" / (stage + ".olean")
            if not source.is_file():
                raise FileNotFoundError("missing resumed stage object " + str(source))
            digest = sha(source)
            if digest != prior_group.get("olean_sha256"):
                raise ValueError("resume object hash mismatch at " + stage)
            dest = output / source.name
            shutil.copy2(source, dest)
            groups.append(prior_group)
            old_stage = stage
        start_offset = len(groups) * chunk_size
        if groups:
            report["staged_root"] = groups[-1]["stage"]
            report["chunks"] = groups
            (work / "report.json").write_text(
                json.dumps(report, indent=2, sort_keys=True) + "\n")
            print(
                f"resumed {len(groups)} authenticated kernel chunks "
                f"({start_offset}/{len(affected_order)} affected modules)",
                flush=True,
            )

    for offset in range(start_offset, len(affected_order), chunk_size):
        group = affected_order[offset:offset + chunk_size]
        chunk_no = offset // chunk_size
        stage = prefix + "Chunk" + format(chunk_no, "04d")
        # One previously checked stage suffices for ALL earlier relocated
        # declarations. Unchanged direct dependencies are imported by name.
        imports = ([] if old_stage is None else [old_stage])
        for module in group:
            for dep in index[module]["imports"]:
                if dep not in affected and dep not in imports:
                    imports.append(dep)
        imports_file = work / (stage + ".imports.txt")
        objects_file = work / (stage + ".objects.txt")
        write_lines(imports_file, imports)
        write_lines(objects_file, [files[m] for m in group])
        dest = output / (stage + ".olean")
        log = work / (stage + ".log")
        with log.open("w") as out:
            p = subprocess.run(
                [str(tool), str(imports_file), str(work / "relocation.txt"),
                 str(objects_file), stage, prefix, str(dest)],
                env=env, stdout=out, stderr=subprocess.STDOUT)
        if p.returncode != 0:
            raise RuntimeError(
                "kernel replay failed at " + stage + ": " +
                log.read_text(errors="replace")[-3500:])
        output_text = log.read_text()
        if not dest.is_file() or "PASS: saved" not in output_text:
            raise RuntimeError("incomplete stage " + stage)
        groups.append({
            "stage": stage, "module_count": len(group),
            "source_modules": group, "olean_sha256": sha(dest),
            "log_tail": output_text.strip().splitlines()[-1]
        })
        old_stage = stage
        report["staged_root"] = stage
        report["chunks"] = groups
        (work / "report.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(stage, groups[-1]["log_tail"], flush=True)

    report["mode"] = "chunked-lean-replay"
    report["chunk_size"] = chunk_size
    report["unchanged_objects_copied"] = copied
    report["complete"] = True
    (work / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    return report, output, names


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--producer-objects", type=Path, required=True)
    p.add_argument("--base", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--root-module", required=True)
    p.add_argument("--root-name", action="append", required=True)
    p.add_argument("--prefix", required=True)
    p.add_argument("--tool", type=Path, required=True)
    p.add_argument("--comparator", type=Path)
    p.add_argument("--comparator-batch", type=Path)
    p.add_argument("--allow-compatible", action="store_true")
    p.add_argument("--chunk-size", type=int, default=64)
    p.add_argument("--resume-from", type=Path)
    a = p.parse_args()
    report, _, _ = relocate_chunked(
        producer_files=a.producer_objects.read_text().splitlines(),
        base=a.base, work=a.work, root_module=a.root_module,
        root_names=a.root_name, prefix=a.prefix, tool=a.tool.resolve(),
        comparator=a.comparator, comparator_batch=a.comparator_batch,
        allow_compatible=a.allow_compatible, chunk_size=a.chunk_size,
        resume_from=a.resume_from)
    print(json.dumps({
        "complete": report["complete"], "mode": report["mode"],
        "staged_root": report["staged_root"],
        "affected_modules": report["affected_modules"],
        "chunks": len(report.get("chunks", []))
    }, sort_keys=True))


if __name__ == "__main__":
    main()
