#!/usr/bin/env python3
"""Consume source-accepted Raw83 and Raw85 Covers after Canonical55."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "im-results" / "agent31-shared-core"))

import assemble_canonical68 as a68
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
BASE_ARTIFACT = "canonical55-raw106-raw79-graft-integrated"
BASE_MODULE = "Canonical55Raw106Raw79Graft"
BASE_REPORT = "canonical55-raw106-raw79-graft.json"

RAW83 = {
    "label": "raw83",
    "run_id": 45755362807,
    "revision": "8d8a3fcc59600146fb25eb70afc2f34a31c99cb3",
    "artifact_id": 15087730774,
    "artifact_name": "raw83-parent-proof",
    "digest": "89ea0f6ae8f0da2d11f86c959b1d848d7c4ef44e933899bfc2654c7dc1a9a1a2",
    "root": "A10Raw83Exact",
    "theorem": "BB6.Agent10Raw83.all_completions",
    "table": "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA",
    "bound": 514,
    "size": 9709805,
}

RAW85 = {
    "label": "raw85",
    "run_id": 45585065939,
    "revision": "52ea69fba34b5f37bbc630392d2dc6dc1d3affbe",
    "artifact_id": 15008641615,
    "artifact_name": "raw85-bound-certified",
    "digest": "a9ff7c78fb926a7a4c172b9a76c2e5a3681268943e312a3adb306930153798c7",
    "root": "Raw85Bound",
    "theorem": "BB6.Agent21Raw85.all_completions",
    "table": "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA",
    "bound": 7014,
    "size": 9435332,
}

NS = "BB6.Agent31Canonical53Raw83Raw85Graft"


def verify_base(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", (run_id, run.get("conclusion"))
    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["name"] == BASE_ARTIFACT]
    assert len(matches) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = matches[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")

    dirs = a68.download((item["id"], run_id, digest), work)
    roots = [
        p for p in work.rglob(BASE_MODULE + ".olean")
        if "metadata" not in p.parts
    ]
    assert len(roots) == 1, [str(p) for p in roots]
    linked = roots[0].parent

    reports = [
        p for p in work.rglob(BASE_REPORT)
        if "metadata" not in p.parts
    ]
    if not reports:
        reports = list((work / "metadata" / str(item["id"])).rglob(BASE_REPORT))
    assert len(reports) == 1, [str(p) for p in reports]
    report_path = reports[0]
    report = json.loads(report_path.read_text())

    assert report["status"] == "source-accepted Canonical57-to-55 Raw106+Raw79 delta"
    assert report["source_revision"] == run["head_sha"]
    assert report["canonical57_residual_count"] == 57
    assert report["remaining_residual_count"] == 55
    assert report["raw106_removed"] and report["raw79_removed"]
    assert report["raw124_already_removed"]
    assert report["olean_sha256"] == a68.sha(linked / (BASE_MODULE + ".olean"))
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return linked, item, digest, report_path, report


def verify_raw85(work: Path):
    spec = RAW85
    run = a68.api_json(f"repos/{REPO}/actions/runs/{spec['run_id']}")
    assert run["conclusion"] == "success", run.get("conclusion")
    assert run["head_sha"] == spec["revision"], (run["head_sha"], spec["revision"])

    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{spec['run_id']}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["id"] == spec["artifact_id"]]
    assert len(matches) == 1, matches
    item = matches[0]
    assert item["name"] == spec["artifact_name"]
    assert item["digest"] == "sha256:" + spec["digest"]
    assert item["size_in_bytes"] == spec["size"]
    assert not item["expired"]

    dirs = a68.download(
        (spec["artifact_id"], spec["run_id"], spec["digest"]), work
    )
    assert any((d / (spec["root"] + ".olean")).is_file() for d in dirs)

    manifests = list((work / "metadata" / str(spec["artifact_id"])).rglob("*.json"))
    candidates = []
    for path in manifests:
        try:
            manifest = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        claim = manifest.get("claim") or {}
        if claim.get("theorem") == spec["theorem"]:
            candidates.append((path, manifest))
    assert len(candidates) == 1, [str(p) for p, _ in candidates]
    manifest_path, manifest = candidates[0]
    assert manifest["proof_source_revision"] == spec["revision"]
    assert manifest["artifact_name"] == spec["artifact_name"]
    assert manifest["claim"]["parent_table"] == spec["table"]
    assert manifest["claim"]["weighted_bound"] == spec["bound"]
    assert "4.36.0-rc2" in manifest["lean_version"]
    compiler = Path(
        subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    ) / "bin" / "lean"
    assert manifest["lean_binary"]["sha256"] == a68.sha(compiler)
    return dirs, manifest_path, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical55-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    assert "4.36.0-rc2" in subprocess.check_output(
        ["lean", "--version"], text=True
    )

    base_work = work / "base"
    raw83_work = work / "raw83"
    raw85_work = work / "raw85"
    base_work.mkdir()
    raw83_work.mkdir()
    raw85_work.mkdir()

    linked, base_item, base_digest, base_report_path, base_report = verify_base(
        base_work, args.canonical55_run_id
    )

    raw83_dirs, raw83_metadata = five.download_parent(RAW83, raw83_work)
    raw85_dirs, raw85_manifest_path, raw85_manifest = verify_raw85(raw85_work)

    copied = []
    audits = {}
    for spec, dirs in ((RAW83, raw83_dirs), (RAW85, raw85_dirs)):
        audit = {}
        selected.add_family(spec, dirs, linked, copied, audit)
        audits[spec["label"]] = audit

    source = HERE / "Canonical53Raw83Raw85Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log_path = work / "canonical53-raw83-raw85-graft.log"
    log = a68.compile_module(source, output, env, log_path)

    required = [
        NS + "." + name for name in (
            "p83_count55", "p85_count55", "p83_p85_distinct",
            "p83_root", "p85_root", "p83_cover", "p85_cover",
            "count53", "p83_removed", "p85_removed",
            "p106_still_removed", "p79_still_removed",
            "sound_integrated", "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical55-base-report.json")
    shutil.copy2(raw85_manifest_path, generated / "raw85-parent-manifest.json")
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(RAW83, indent=2, sort_keys=True) + "\n"
    )

    report = {
        "status": "source-accepted Canonical55-to-53 Raw83+Raw85 delta",
        "canonical55_run_id": args.canonical55_run_id,
        "canonical55_artifact_id": base_item["id"],
        "canonical55_artifact_name": base_item["name"],
        "canonical55_artifact_sha256": base_digest,
        "canonical55_source_revision": base_report["source_revision"],
        "canonical55_residual_count": 55,
        "canonical55_olean_sha256": base_report["olean_sha256"],
        "raw83_parent": raw83_metadata,
        "raw85_parent": RAW85,
        "raw83_link_audit": audits["raw83"],
        "raw85_link_audit": audits["raw85"],
        "raw83_unique_membership_in_canonical55": True,
        "raw85_unique_membership_in_canonical55": True,
        "raw83_raw85_distinct": True,
        "raw83_removed": True,
        "raw85_removed": True,
        "raw106_still_removed": True,
        "raw79_still_removed": True,
        "raw124_already_removed": True,
        "remaining_residual_count": 53,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    report_path = work / "canonical53-raw83-raw85-graft.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
