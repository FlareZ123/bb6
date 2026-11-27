#!/usr/bin/env python3
"""Detect cross-module kernel declaration collisions in selected Lean objects.

Run AFTER ordinary module identity/provenance checks and BEFORE elaborating a
large consumer. A clean scan is not a source or proof acceptance gate.
"""
import argparse
from collections import defaultdict
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
BATCH_BYTES = 256 * 1024 * 1024


def batches(paths, limit):
    """Bound mapped object bytes per short-lived Lean reader (except one big file)."""
    if limit <= 0:
        raise ValueError("batch size must be positive")
    batch, size = [], 0
    for path in paths:
        n = path.stat().st_size
        if batch and (size + n > limit or len(batch) == 128):
            yield batch
            batch, size = [], 0
        batch.append(path)
        size += n
    if batch:
        yield batch


def audit_objects(objects, families, *, lean="lean", batch_bytes=BATCH_BYTES):
    """objects: selected module filename -> object path (one per module).

    families: label -> {roots: [...], files: [paths from reached closure]}.
    Record overlaps by structural Name, not display spelling. Repeated imports
    of the SAME module are intentionally collapsed. Lean allows some theorem
    and axiom overlaps; those require an actual combined import, not rejection
    or an assumption of equality based on name alone.
    """
    selected = {name: Path(path).resolve(strict=True) for name, path in objects.items()}
    if not selected or len(set(selected.values())) != len(selected):
        raise ValueError("expected nonempty, uniquely selected project modules")
    if any(p.suffix != ".olean" or p.name != name for name, p in selected.items()):
        raise ValueError("expected single-part .olean objects")
    paths = {str(path): name for name, path in selected.items()}
    memberships = defaultdict(set)
    for label, family in families.items():
        for path in family["files"]:
            # The common linker stores one path per flat module, possibly from
            # another byte/kernel-equal artifact family. Use its module key.
            name = Path(path).name
            if name not in selected:
                raise ValueError(f"reached module absent from selected objects: {name}")
            memberships[name].add(label)
    if set(memberships) != set(selected):
        raise ValueError("reached-family inventory differs from selected objects")
    first = {}
    overlaps = {}
    total = 0
    for batch in batches(sorted(selected.values()), batch_bytes):
        raw = subprocess.check_output(
            [lean, "--run", str(HERE / "AuditDeclOwners.lean"), *map(str, batch)],
            text=True,
        )
        seen = set()
        for line in raw.splitlines():
            path, declarations = json.loads(line)
            module = paths[path]
            if path in seen:
                raise ValueError(f"repeated reader output: {path}")
            seen.add(path)
            for parts, display, kind in declarations:
                key = tuple(sys.intern(part) if isinstance(part, str) else part for part in parts)
                if kind not in {"other", "axiom", "theorem"}:
                    raise ValueError(f"unknown declaration kind: {kind}")
                owner = (module, kind)
                total += 1
                previous = first.setdefault(key, owner)
                if previous[0] != module:
                    row = overlaps.setdefault(key, {"name": display, "key": parts,
                                                      "owners": {previous}})
                    row["owners"].add(owner)
        if seen != set(map(str, batch)):
            raise ValueError("reader did not enumerate every requested module")
    rows = []
    for row in overlaps.values():
        owners = sorted(row["owners"])
        rows.append({"name": row["name"], "name_components": row["key"],
                     "classification": ("incompatible_non_theorem_or_axiom"
                                        if any(kind == "other" for _, kind in owners)
                                        else "requires_combined_import"),
                     "owners": [{"module": module, "kind": kind,
                                 "path": str(selected[module]),
                                 "families": [{"label": label,
                                               "roots": families[label]["roots"]}
                                              for label in sorted(memberships[module])]}
                                for module, kind in owners]})
    rows.sort(key=lambda r: (r["name"], repr(r["name_components"])))
    hard = sum(r["classification"] == "incompatible_non_theorem_or_axiom" for r in rows)
    return {"module_count": len(selected), "declaration_count": total,
            "definite_conflict_count": hard,
            "requires_import_check_count": len(rows) - hard,
            "overlaps": rows}


def audit_linked_roots(linked, roots, *, lean="lean", batch_bytes=BATCH_BYTES, smoke=True):
    """Inspect exactly the project import closures of these roots in one flat link."""
    linked = Path(linked).resolve(strict=True)
    roots = list(dict.fromkeys(roots))
    if not roots or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", r) for r in roots):
        raise ValueError("expected flat project root module names")
    stdlib = Path(subprocess.check_output([lean, "--print-prefix"], text=True).strip()) / "lib/lean"
    families, objects = {}, {}
    for root in roots:
        raw = subprocess.check_output([lean, "--run", str(HERE / "WalkImportClosure.lean"),
                                       str(stdlib), "1", str(linked), root], text=True)
        files = sorted(set(raw.splitlines()))
        if str(linked / (root + ".olean")) not in files:
            raise ValueError(f"root is not a selected project object: {root}")
        for path in files:
            p = Path(path)
            if p.parent != linked:
                raise ValueError(f"expected flat project object: {p}")
            objects[p.name] = p
        families[root] = {"roots": [root], "files": files}
    report = audit_objects(objects, families, lean=lean, batch_bytes=batch_bytes)
    report["roots"] = roots
    report["smoke"] = {"status": "not_run"}
    if report["definite_conflict_count"]:
        report["status"] = "definite_conflict"
    elif smoke:
        with tempfile.TemporaryDirectory(prefix="bb6-import-smoke-") as directory:
            source = Path(directory) / "ImportSmoke.lean"
            source.write_text("".join(f"import {root}\n" for root in roots))
            result = subprocess.run([lean, str(source)], cwd=directory,
                                    env=dict(os.environ, LEAN_PATH=str(linked)),
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        report["smoke"] = {"status": "passed" if result.returncode == 0 else "failed",
                           "returncode": result.returncode, "output": result.stdout}
        report["status"] = "import_passed" if result.returncode == 0 else "import_failed"
    else:
        report["status"] = "scan_only"
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--linked", type=Path, required=True)
    ap.add_argument("--root", action="append", required=True)
    ap.add_argument("--report", type=Path, required=True)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--batch-bytes", type=int, default=BATCH_BYTES)
    ap.add_argument("--scan-only", action="store_true")
    args = ap.parse_args()
    report = audit_linked_roots(args.linked, args.root, lean=args.lean,
                                batch_bytes=args.batch_bytes, smoke=not args.scan_only)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{report['status']}: {report['module_count']} modules, "
          f"{report['definite_conflict_count']} definite conflicts, "
          f"{report['requires_import_check_count']} theorem/axiom overlaps")
    if report["status"] in {"definite_conflict", "import_failed"}:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
