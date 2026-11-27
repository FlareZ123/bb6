#!/usr/bin/env python3
"""Strict source/object merge for the four disjoint original-source Raw36 shards.

The 20 machine-bounded leaves have been proved independently against the
same Lean rc2 compiler.  This merger checks full source+object+import-closure
identities and refuses nonidentical common imports.  No .olean is patched.
The resulting manifest can be fed directly to lean_compile_closure.py's
--precompiled-manifest/--precompiled-dir interface for the thin parent.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

GROUPS = ((0, 1, 2, 3, 4), (6, 7, 8, 9, 10),
          (12, 13, 14, 15, 16), (18, 19, 20, 21, 22))


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as f:
        for part in iter(lambda: f.read(1 << 20), b""):
            digest.update(part)
    return digest.hexdigest()


def encoded(payload) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()


def check_file(src: Path, expected: str) -> None:
    assert src.is_file(), src
    assert sha(src) == expected, f"SHA mismatch: {src}"


def safe_module(name: str) -> Path:
    assert re.fullmatch(r"[A-Za-z0-9_.]+", name), name
    return Path(*name.split("."))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True,
                    help="directory of raw36-shard-0 through raw36-shard-3")
    ap.add_argument("--merged", type=Path, required=True)
    args = ap.parse_args()
    dest = args.merged
    dest.mkdir(parents=True, exist_ok=False)
    base = None
    members = {}
    roots = {}
    expected_provenance = None
    for i, children in enumerate(GROUPS):
        source_dir = args.inputs / f"raw36-shard-{i}"
        manifest = json.loads((source_dir / "manifest.json").read_text())
        assert manifest["schema_version"] == 1
        assert manifest["label"] == f"raw36-shard-{i}"
        assert manifest["claim"]["weighted_bound"] == 162
        assert manifest["module_count"] == len(manifest["modules"])
        expected_roots = {f"Raw36Kid{j:02d}" for j in children}
        assert {r["module"] for r in manifest["roots"]} == expected_roots
        assert len(manifest["roots"]) == len(expected_roots)
        inputs = {e["path"]:e["sha256"] for e in manifest["provenance_inputs"]}
        if base is None:
            base = manifest
            expected_provenance = inputs
        else:
            for key in ("lean_version", "lean_binary",
                        "proof_source_revision"):
                assert (base[key] == manifest[key]), (i, key)
            assert inputs == expected_provenance, (i,"provenance")
        for entry in manifest["modules"]:
            module = entry["module"]
            rel = safe_module(module)
            olean_rel = rel.with_suffix(".olean")
            lean_rel = rel.with_suffix(".lean")
            assert str(olean_rel) == entry["olean_path"], module
            olean = source_dir / olean_rel
            src = source_dir / lean_rel
            check_file(src,entry["source_sha256"])
            check_file(olean,entry["olean_sha256"])
            assert isinstance(entry["project_imports"], list)
            if module in members:
                assert members[module] == entry, f"conflicting module {module}"
            else:
                members[module] = entry
            for relp, origin in ((lean_rel,src),(olean_rel,olean)):
                target = dest / relp
                if target.exists():
                    assert sha(target) == sha(origin), (i,relp)
                else:
                    target.parent.mkdir(parents=True,exist_ok=True)
                    shutil.copy2(origin,target)
        for root in manifest["roots"]:
            module = root["module"]
            assert module not in roots, module
            assert module in members, module
            assert root["source_sha256"] == members[module]["source_sha256"]
            roots[module] = root

    assert len(roots) == 20
    assert set(roots) == {f"Raw36Kid{i:02d}" for g in GROUPS for i in g}
    identities = {}
    def identity(module: str):
        if module in identities:
            return identities[module]
        entry = members[module]
        deps = []
        for dep in sorted(entry["project_imports"]):
            assert dep in members, (module, dep)
            deps.append({"module": dep, "identity": identity(dep)})
        import_hash = hashlib.sha256(encoded(deps)).hexdigest()
        assert entry["import_closure_sha256"] == import_hash, module
        payload = {
            "module": module,
            "source_sha256": entry["source_sha256"],
            "project_imports": entry["project_imports"],
            "olean_sha256": entry["olean_sha256"],
            "import_closure_sha256": import_hash,
        }
        result = hashlib.sha256(encoded(payload)).hexdigest()
        assert entry["module_identity_sha256"] == result, module
        identities[module] = result
        return result

    for module in sorted(members):
        identity(module)
    result = dict(base)
    result["label"] = "raw36-20-representative-merged"
    result["artifact_name"] = "raw36-20-representative-merged"
    result["roots"] = [roots[m] for m in sorted(roots)]
    result["modules"] = [members[m] for m in sorted(members)]
    result["module_count"] = len(members)
    result["claim"] = {
        "theorem": "BB6.Agent29Raw36.branch_bound",
        "parent_table": "1RB---_1RC0LA_0RD---_0LD1LB_------_------",
        "weighted_bound": 162,
    }
    (dest / "manifest.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("PASS:", len(roots), "accepted child roots,",
          len(members), "dependency-closed pinned modules merged, standard Lean rc2 axioms only",
          flush=True)


if __name__ == "__main__":
    main()
