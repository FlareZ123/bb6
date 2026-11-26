#!/usr/bin/env python3
"""Compare Lean-exported Canonical58/57 rosters with the source crosswalk, exactly."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
CROSSWALK = ROOT / "im-results/agent31-canonical58-source-crosswalk/crosswalk.json"
ROSTER = ROOT / "im-results/agent13-roster-convergence/canonical-124.json"
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"


def encode_rle(table):
    if len(table) != 12:
        raise AssertionError(f"expected 12 cells, got {len(table)}")
    tokens = ["---" if cell is None else cell for cell in table]
    return "_".join(tokens[i] + tokens[i + 1] for i in range(0, 12, 2))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize(rows, label):
    if not isinstance(rows, list):
        raise AssertionError(f"{label} export is not a list")
    normalized = []
    for row in rows:
        raw_index = int(row["raw_residual_index"])
        table_rle = row["table_rle"]
        if not isinstance(table_rle, str) or len(table_rle.replace("_", "")) != 36:
            raise AssertionError(f"invalid six-state table for raw index {raw_index}: {table_rle}")
        normalized.append((raw_index, table_rle))
    ids = [raw for raw, _ in normalized]
    if len(ids) != len(set(ids)):
        raise AssertionError(f"{label} export contains duplicate raw indices")
    return normalized


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    args = parser.parse_args()
    work = args.work.resolve()

    crosswalk = json.loads(CROSSWALK.read_text())
    raw_roster = json.loads(ROSTER.read_text())
    source_by_raw = {
        int(entry["raw_residual_index"]): entry for entry in raw_roster["entries"]
    }
    expected_manifest = crosswalk.get("current_roster_manifest")
    if not isinstance(expected_manifest, list):
        raise AssertionError("crosswalk report lacks current_roster_manifest")

    expected_from_source = []
    for raw_index in crosswalk["current_roster_raw_indices"]:
        entry = source_by_raw[int(raw_index)]
        expected_from_source.append({
            "raw_residual_index": int(raw_index),
            "canonical_index": int(entry["canonical_index"]),
            "holes": int(entry["holes"]),
            "address": [step["move"] for step in entry["address"]],
            "table_rle": encode_rle(entry["table"]),
        })
    expected_from_source.sort(key=lambda x: x["raw_residual_index"])
    expected_manifest = sorted(expected_manifest, key=lambda x: int(x["raw_residual_index"]))
    if expected_manifest != expected_from_source:
        raise AssertionError("crosswalk's committed manifest disagrees with its canonical-124 source")

    lean58_path = work / "canonical58-lean-roster.json"
    lean57_path = work / "canonical57-lean-roster.json"
    lean58 = json.loads(lean58_path.read_text())
    lean57 = json.loads(lean57_path.read_text())

    expected58_pairs = normalize(
        [{"raw_residual_index": x["raw_residual_index"], "table_rle": x["table_rle"]}
         for x in expected_manifest],
        "expected Canonical58",
    )
    actual58_pairs = normalize(lean58, "Lean Canonical58")
    if Counter(expected58_pairs) != Counter(actual58_pairs):
        missing = sorted((Counter(expected58_pairs) - Counter(actual58_pairs)).elements())
        extra = sorted((Counter(actual58_pairs) - Counter(expected58_pairs)).elements())
        raise AssertionError(f"Lean Canonical58 roster mismatch: missing={missing}, extra={extra}")
    if len(actual58_pairs) != 58:
        raise AssertionError(f"Lean Canonical58 export has {len(actual58_pairs)} entries, expected 58")

    expected_ids = {raw for raw, _ in expected58_pairs}
    actual_ids = {raw for raw, _ in actual58_pairs}
    if 59 not in expected_ids or 59 not in actual_ids:
        raise AssertionError("Raw59 must be retained in the accepted Canonical58 roster")
    if 118 in expected_ids or 118 in actual_ids:
        raise AssertionError("Raw118 must be absent from the accepted Canonical58 roster")

    raw112_matches = [x for x in expected_manifest if x["table_rle"] == RAW112_TABLE]
    if len(raw112_matches) != 1:
        raise AssertionError(f"Raw112 table must occur exactly once in Canonical58, got {len(raw112_matches)}")
    expected57_manifest = [x for x in expected_manifest if x["table_rle"] != RAW112_TABLE]
    expected57_pairs = normalize(
        [{"raw_residual_index": x["raw_residual_index"], "table_rle": x["table_rle"]}
         for x in expected57_manifest],
        "expected Canonical57",
    )
    actual57_pairs = normalize(lean57, "Lean Canonical57")
    if Counter(expected57_pairs) != Counter(actual57_pairs):
        missing = sorted((Counter(expected57_pairs) - Counter(actual57_pairs)).elements())
        extra = sorted((Counter(actual57_pairs) - Counter(expected57_pairs)).elements())
        raise AssertionError(f"Lean Canonical57 roster mismatch: missing={missing}, extra={extra}")
    if len(actual57_pairs) != 57:
        raise AssertionError(f"Lean Canonical57 export has {len(actual57_pairs)} entries, expected 57")
    if any(table == RAW112_TABLE for _, table in actual57_pairs):
        raise AssertionError("Raw112 must be absent from Canonical57")
    if 59 not in {raw for raw, _ in actual57_pairs} or 118 in {raw for raw, _ in actual57_pairs}:
        raise AssertionError("Canonical57 must retain Raw59 and exclude Raw118")

    metadata_by_raw = {int(x["raw_residual_index"]): x for x in expected_manifest}
    enriched58 = [
        {**metadata_by_raw[raw], "lean_table_rle": table}
        for raw, table in sorted(actual58_pairs)
    ]
    enriched57 = [
        {**metadata_by_raw[raw], "lean_table_rle": table}
        for raw, table in sorted(actual57_pairs)
    ]

    graft_path = work / "canonical57-raw112-graft.json"
    graft = json.loads(graft_path.read_text())
    source_revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    lean_export_source = ROOT / "im-results/agent32-raw59/Canonical58RosterExport.lean"
    crosswalk_source = CROSSWALK.parent / "crosswalk.py"
    source_hashes = {
        "lean_export_source_sha256": sha(lean_export_source),
        "comparison_script_sha256": sha(Path(__file__).resolve()),
        "crosswalk_script_sha256": sha(crosswalk_source),
        "canonical124_source_sha256": sha(ROSTER),
    }
    base = {
        "canonical58_run_id": graft["canonical58_base_run_id"],
        "canonical58_artifact_id": graft["canonical58_artifact_id"],
        "canonical58_artifact_sha256": graft["canonical58_artifact_sha256"],
        "canonical58_source_revision": graft["canonical58_source_revision"],
        "canonical58_olean_sha256": graft["canonical58_olean_sha256"],
    }
    successor = {
        "canonical57_graft_source_revision": graft["source_revision"],
        "canonical57_graft_olean_sha256": graft["graft_olean_sha256"],
        "raw112_run_id": graft["raw112_run_id"],
        "raw112_artifact_id": graft["raw112_artifact_id"],
        "raw112_artifact_sha256": graft["raw112_artifact_sha256"],
    }

    manifest58 = {
        "status": "exact Lean-exported Canonical58 partial-table manifest",
        **base,
        "crosswalk_source_repo_head": crosswalk["source_repo_head"],
        "crosswalk_inputs": crosswalk["inputs"],
        "raw59_retained": True,
        "raw118_absent": True,
        "raw112_present": True,
        **source_hashes,
        "lean_toolchain": os.environ.get("LEAN_VERSION", "not supplied"),
        "entries": enriched58,
    }
    manifest57 = {
        "status": "exact Lean-exported Canonical57 partial-table manifest",
        **base,
        **successor,
        "crosswalk_source_repo_head": crosswalk["source_repo_head"],
        "crosswalk_inputs": crosswalk["inputs"],
        "raw59_retained": True,
        "raw118_absent": True,
        "raw112_removed": True,
        "raw112_table": RAW112_TABLE,
        **source_hashes,
        "lean_toolchain": os.environ.get("LEAN_VERSION", "not supplied"),
        "entries": enriched57,
    }
    audit = {
        "status": "passed",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "audit_source_revision": source_revision,
        **base,
        **successor,
        "canonical58_count": len(actual58_pairs),
        "canonical58_exact_table_and_multiplicity_match": True,
        "canonical57_count": len(actual57_pairs),
        "canonical57_exact_table_and_multiplicity_match": True,
        "raw59_retained": True,
        "raw118_absent": True,
        "raw112_removed": True,
        "raw112_table": RAW112_TABLE,
        "crosswalk_source_repo_head": crosswalk["source_repo_head"],
        "crosswalk_inputs": crosswalk["inputs"],
        **source_hashes,
        "lean_toolchain": os.environ.get("LEAN_VERSION", "not supplied"),
        "lean58_export_sha256": sha(lean58_path),
        "lean57_export_sha256": sha(lean57_path),
        "canonical58_manifest_sha256": None,
        "canonical57_manifest_sha256": None,
    }

    out58 = work / "canonical58-lean-roster-manifest.json"
    out57 = work / "canonical57-lean-roster-manifest.json"
    out58.write_text(json.dumps(manifest58, indent=2) + "\n")
    out57.write_text(json.dumps(manifest57, indent=2) + "\n")
    audit["canonical58_manifest_sha256"] = sha(out58)
    audit["canonical57_manifest_sha256"] = sha(out57)
    (work / "canonical58-roster-crosswalk-audit.json").write_text(
        json.dumps(audit, indent=2) + "\n"
    )
    print(json.dumps(audit, indent=2))


if __name__ == "__main__":
    main()
