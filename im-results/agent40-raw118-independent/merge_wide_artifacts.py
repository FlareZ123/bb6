#!/usr/bin/env python3
"""Rehydrate and merge source-checked Raw118 wide-certificate artifacts."""
from pathlib import Path
import hashlib
import json
import shutil
import sys

HERE = Path(__file__).resolve().parent
IM = HERE.parent
A1 = IM / "agent1-bidfa-sat"
sys.path.insert(0, str(A1))
import wide_cert

IDENTITY_FIELDS = (
    "source_sha256", "project_imports", "olean_sha256",
    "import_closure_sha256", "module_identity_sha256",
)


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def merge(artifacts_root: Path, precompiled_dir: Path, source_root: Path) -> None:
    widths = json.loads((A1 / "raw118-wide-widths.json").read_text())
    expected = {int(i) for i in widths}
    roster = {
        int(i): table
        for i, table in (
            line.split()
            for line in (A1 / "raw118-hard87.tsv").read_text().splitlines()
            if line.strip()
        )
    }
    sat = json.loads((A1 / "raw118-sat-hits.json").read_text())
    sat_ids = {int(x["index"]) for x in sat}
    assert len(expected) == 47
    assert not (expected & sat_ids)

    artifact_dirs = sorted(p for p in artifacts_root.iterdir() if p.is_dir())
    witnesses = {}
    manifests = []
    for artifact_dir in artifact_dirs:
        witness_path = artifact_dir / "witness.json"
        manifest_path = artifact_dir / "manifest.json"
        audit_path = artifact_dir / "audit.log"
        assert witness_path.is_file() and manifest_path.is_file() and audit_path.is_file(), artifact_dir
        witness = json.loads(witness_path.read_text())
        i = int(witness["index"])
        assert i in expected and i not in witnesses, (i, artifact_dir)
        assert witness["table"] == roster[i], (i, witness["table"], roster[i])
        audit = audit_path.read_text(errors="replace")
        assert "sorryAx" not in audit and "native_decide" not in audit, (i, "axiom audit")
        states, edges = wide_cert.emit(
            i, witness["table"], witness["left"], witness["right"], source_root
        )
        assert states == int(witness["states"]), (i, states, witness["states"])
        assert edges == int(witness["edges"]), (i, edges, witness["edges"])
        witnesses[i] = witness
        manifests.append((artifact_dir, json.loads(manifest_path.read_text())))

    assert set(witnesses) == expected, (
        sorted(expected - set(witnesses)), sorted(set(witnesses) - expected)
    )
    assert len(artifact_dirs) == len(expected)

    precompiled_dir.mkdir(parents=True, exist_ok=True)
    source_root.mkdir(parents=True, exist_ok=True)
    merged_modules = {}
    merged_roots = {}
    merged_inputs = {}
    source_revisions = set()
    first = manifests[0][1]

    for artifact_dir, manifest in manifests:
        assert manifest["schema_version"] == first["schema_version"] == 1
        assert manifest["lean_version"] == first["lean_version"]
        assert manifest["lean_binary"]["sha256"] == first["lean_binary"]["sha256"]
        assert manifest["proof_source_revision"] == first["proof_source_revision"]
        assert manifest["workflow"]["run_id"] == first["workflow"]["run_id"]
        source_revisions.update(manifest.get("source_revisions", []))

        for root in manifest["roots"]:
            key = root["module"]
            if key in merged_roots:
                assert merged_roots[key]["source_sha256"] == root["source_sha256"], key
            else:
                merged_roots[key] = root

        for item in manifest["provenance_inputs"]:
            key = item["path"]
            if key in merged_inputs:
                assert merged_inputs[key] == item["sha256"], key
            else:
                merged_inputs[key] = item["sha256"]

        for item in manifest["modules"]:
            module = item["module"]
            if module in merged_modules:
                for field in IDENTITY_FIELDS:
                    assert merged_modules[module][field] == item[field], (module, field)
            else:
                merged_modules[module] = item

            rel = Path(item["olean_path"])
            src = artifact_dir / rel
            assert src.is_file(), (artifact_dir, rel)
            assert sha(src) == item["olean_sha256"], (module, "artifact olean hash")
            dst = precompiled_dir / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            if dst.exists():
                assert sha(dst) == item["olean_sha256"], (module, "duplicate olean hash")
            else:
                shutil.copy2(src, dst)

    for module, item in merged_modules.items():
        if module.startswith("Raw118Wide"):
            src = source_root / f"{module}.lean"
            assert src.is_file(), (module, src)
            assert sha(src) == item["source_sha256"], (module, "regenerated source hash")

    merged = dict(first)
    merged["label"] = "merged Raw118 wide-window proof closures"
    merged["artifact_name"] = "raw118-wide-merged"
    merged["claim"] = {
        "theorem": "47 source-checked Raw118 wide-window nonhalting certificates",
        "parent_table": None,
        "weighted_bound": None,
    }
    merged["source_revisions"] = sorted(source_revisions)
    merged["roots"] = [merged_roots[k] for k in sorted(merged_roots)]
    merged["provenance_inputs"] = [
        {"path": k, "sha256": merged_inputs[k]} for k in sorted(merged_inputs)
    ]
    merged["modules"] = [merged_modules[k] for k in sorted(merged_modules)]
    merged["module_count"] = len(merged["modules"])
    merged["precompiled_core"] = None
    (precompiled_dir / "manifest.json").write_text(json.dumps(merged, indent=2) + "\n")
    print(
        f"merged {len(witnesses)} wide proofs; {len(merged_modules)} modules; "
        f"{len(merged_roots)} roots; source_root={source_root}; precompiled={precompiled_dir}"
    )


if __name__ == "__main__":
    if len(sys.argv) != 4:
        raise SystemExit("usage: merge_wide_artifacts.py ARTIFACTS PRECOMPILED_DIR SOURCE_ROOT")
    merge(Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]))
