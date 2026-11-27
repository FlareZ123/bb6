#!/usr/bin/env python3
"""Consume source-accepted Raw95/103/105 exact parents after Canonical50."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "im-results" / "agent31-shared-core"))

import assemble_canonical49_raw59_after_eight as c49
import assemble_canonical68 as a68
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
SHARP_RUN = 45919568346
SHARP_REVISION = "fc71d53353958fd92100191242692dbcbfe00360"

SPECS = {
    "95": {
        "label": "raw95",
        "artifact_id": 15164121806,
        "artifact_name": "raw95-sharp-certified",
        "digest": "e92d33dd6dffa3bf8acf7cd5cd2d90e9f08a00c4fed5581615ea45e71ae0aebe",
        "size": 8928677,
        "root": "SharpRaw95",
        "theorem": "BB6.Agent31SharpRaw95.exact95",
        "bound": 379,
    },
    "103": {
        "label": "raw103",
        "artifact_id": 15163277898,
        "artifact_name": "raw103-sharp-certified",
        "digest": "092804dd1873c2db40247ce33c06f14234cad8e62f257f07fc488e819f4f7551",
        "size": 6465751,
        "root": "Raw103Data",
        "theorem": "BB6.Agent3Raw103.exact103",
        "bound": 116,
    },
    "105": {
        "label": "raw105",
        "artifact_id": 15164195888,
        "artifact_name": "raw105-sharp-certified",
        "digest": "53fd0f80323fca1cd4b6afeebbb89ff7813be83acb3527437d64e8558d0039a9",
        "size": 8384849,
        "root": "SharpRaw105",
        "theorem": "BB6.Agent31SharpRaw105.exact105",
        "bound": 182,
    },
}

NS = "BB6.Agent31Canonical47SharpParents"


def verify_sharp(raw: str, work: Path):
    spec = SPECS[raw]
    run = a68.api_json(f"repos/{REPO}/actions/runs/{SHARP_RUN}")
    assert run["head_sha"] == SHARP_REVISION, (run["head_sha"], SHARP_REVISION)

    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{SHARP_RUN}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["id"] == spec["artifact_id"]]
    assert len(matches) == 1, matches
    item = matches[0]
    assert item["name"] == spec["artifact_name"], item["name"]
    assert item["digest"] == "sha256:" + spec["digest"], item["digest"]
    assert item["size_in_bytes"] == spec["size"], item["size_in_bytes"]
    assert not item["expired"]
    assert item["workflow_run"]["head_sha"] == SHARP_REVISION

    dirs = a68.download(
        (spec["artifact_id"], SHARP_RUN, spec["digest"]), work
    )
    roots = [
        p for p in work.rglob(spec["root"] + ".olean")
        if "metadata" not in p.parts
    ]
    assert len(roots) == 1, [str(p) for p in roots]

    candidates = []
    for path in work.rglob("*.json"):
        if "metadata" in path.parts:
            continue
        try:
            manifest = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        claim = manifest.get("claim") or {}
        if claim.get("theorem") == spec["theorem"]:
            candidates.append((path, manifest))
    assert len(candidates) == 1, [str(p) for p, _ in candidates]
    manifest_path, manifest = candidates[0]
    assert manifest["proof_source_revision"] == SHARP_REVISION
    assert "4.36.0-rc2" in manifest["lean_version"]
    assert manifest["claim"]["theorem"] == spec["theorem"]
    assert manifest["claim"]["weighted_bound"] == spec["bound"]
    assert any(x["module"] == spec["root"] for x in manifest["roots"])
    root_entry = next(x for x in manifest["modules"] if x["module"] == spec["root"])
    assert root_entry["olean_sha256"] == a68.sha(roots[0])

    compiler = Path(
        subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    ) / "bin" / "lean"
    assert manifest["lean_binary"]["sha256"] == a68.sha(compiler)
    return dirs, item, manifest_path, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical50-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    base_work = work / "base"
    base_work.mkdir()
    sharp_work = {raw: work / ("raw" + raw) for raw in SPECS}
    for d in sharp_work.values():
        d.mkdir()

    linked, base_item, base_digest, base_report_path, base_report = (
        c49.verify_canonical50(base_work, args.canonical50_run_id)
    )

    family_inputs = []
    sharp_meta = {}
    for raw in ("95", "103", "105"):
        dirs, item, manifest_path, manifest = verify_sharp(raw, sharp_work[raw])
        family_inputs.append((SPECS[raw], dirs))
        sharp_meta[raw] = {
            "artifact_id": item["id"],
            "manifest_path": manifest_path,
            "manifest_sha256": a68.sha(manifest_path),
        }

    copied = []
    audits = {}
    for spec, dirs in family_inputs:
        audit = {}
        selected.add_family(spec, dirs, linked, copied, audit)
        audits[spec["label"]] = audit

    source = HERE / "Canonical47SharpParentsGraft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(
        source, output, env, work / "canonical47-sharp-parents.log"
    )

    required = [
        NS + "." + name for name in (
            "p95_count50", "p103_count50", "p105_count50",
            "parents_pairwise_distinct",
            "p95_cover", "p103_cover", "p105_cover",
            "count47", "all_sharp_parents_removed", "raw59_retained",
            "sound_integrated", "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical50-base-report.json")
    for raw, meta in sharp_meta.items():
        shutil.copy2(meta["manifest_path"], generated / f"raw{raw}-parent-manifest.json")

    report = {
        "status": "source-accepted Canonical50-to-47 Raw95+Raw103+Raw105 delta",
        "lean_version": lean_version,
        "canonical50_run_id": args.canonical50_run_id,
        "canonical50_artifact_id": base_item["id"],
        "canonical50_artifact_name": base_item["name"],
        "canonical50_artifact_sha256": base_digest,
        "canonical50_source_revision": base_report["source_revision"],
        "canonical50_residual_count": 50,
        "canonical50_olean_sha256": base_report["olean_sha256"],
        "sharp_run_id": SHARP_RUN,
        "sharp_source_revision": SHARP_REVISION,
        "parents": {
            raw: {**SPECS[raw], **sharp_meta[raw]}
            for raw in ("95", "103", "105")
        },
        "link_audits": audits,
        "all_three_unique_membership_in_canonical50": True,
        "all_three_pairwise_distinct": True,
        "raw59_retained": True,
        "remaining_residual_count": 47,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    report_path = work / "canonical47-sharp-parents.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    packaged = work / "linked"
    assert not packaged.exists(), packaged
    linked.rename(packaged)
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
