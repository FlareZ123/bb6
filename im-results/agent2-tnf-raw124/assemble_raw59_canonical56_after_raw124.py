#!/usr/bin/env python3
"""Consume the staged Raw59 Cover after the accepted Raw124 Canonical57 graft."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))

import assemble_canonical68 as a68
import assemble_canonical59_raw59_graft as raw59

REPO = "FlareZ123/bb6"
BASE_RUN = 45910336799
BASE_ARTIFACT = "canonical58-raw113-graft-integrated"
BASE_ARTIFACT_ID = 15159933665
BASE_ARTIFACT_SHA = "7c912dc7cff20dd796dad9e0008c6fbc9558f81bc9dcc13eb399b4393a73e140"
BASE_ARTIFACT_SIZE = 22949946864
BASE_SOURCE_REVISION = "8f91f38a2ac75dbb2adef4ca82feb4ec694ef26e"
RAW124_PARENT_RUN = 45908591612
RAW124_PARENT_ARTIFACT_ID = 15159377345
RAW124_PARENT_ARTIFACT_SHA = "9ec5b5b86fe4f78d636fd9a37891cabdd0017c04c8fc62f74f4ef6022ffcfa15"
NS = "BB6.Agent2Canonical56Raw59AfterRaw124"


def verify_base(work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    assert run["head_sha"] == BASE_SOURCE_REVISION, (run["head_sha"], BASE_SOURCE_REVISION)
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    matches = [x for x in artifacts if x["name"] == BASE_ARTIFACT]
    assert len(matches) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = matches[0]
    assert item["id"] == BASE_ARTIFACT_ID, item["id"]
    assert item["size_in_bytes"] == BASE_ARTIFACT_SIZE, item["size_in_bytes"]
    assert item["digest"] == "sha256:" + BASE_ARTIFACT_SHA, item["digest"]
    assert not item["expired"], item["id"]

    dirs = a68.download((item["id"], run_id, BASE_ARTIFACT_SHA), work)
    # The pinned producer accepted Raw113, but its optional Raw124 shell
    # command failed (argparse exit 2). Reuse the accepted 58 closure and
    # execute ONLY the missing Raw124 consumer, with its original gates.
    roots = [p for p in dirs if (p / "Canonical58Raw113Graft.olean").is_file()]
    assert len(roots) == 1, [str(p) for p in roots]
    linked = roots[0]
    metadata = work / "metadata" / str(item["id"])
    reports58 = list(metadata.rglob("canonical58-raw113-graft.json"))
    assert len(reports58) == 1, [str(p) for p in reports58]
    report58 = json.loads(reports58[0].read_text())
    assert report58["source_revision"] == run["head_sha"]
    assert report58["remaining_residual_count"] == 58
    assert report58["raw59_retained"]
    assert set(report58["base_accepted"]) == {"raw119", "raw115", "raw58", "raw108", "raw118"}
    assert report58["olean_sha256"] == a68.sha(linked / "Canonical58Raw113Graft.olean")
    shutil.copy2(reports58[0], work / "canonical58-raw113-graft.json")

    graft = linked / "Raw124Canonical58Membership.olean"
    reports57 = list(metadata.rglob("raw124-canonical58-membership.json"))
    if not graft.exists():
        assert not reports57, [str(p) for p in reports57]
        subprocess.run(
            [sys.executable, str(HERE / "assemble_raw124_canonical57.py"),
             "--work", str(work), "--raw124-run-id", str(RAW124_PARENT_RUN)],
            check=True,
        )
        report_path = work / "raw124-canonical58-membership.json"
    else:
        # a68.download extracts JSON exclusively under metadata/.
        assert len(reports57) == 1, [str(p) for p in reports57]
        report_path = reports57[0]
    assert graft.is_file()
    assert (linked / "Raw124ParentComplete.olean").is_file()
    assert report_path.is_file()
    report = json.loads(report_path.read_text())
    assert report["status"] == "source-accepted Canonical58-to-57 Raw124 delta"
    assert report["canonical58_source_revision"] == run["head_sha"]
    assert report["canonical58_residual_count"] == 58
    assert report["canonical57_residual_count"] == 57
    assert report["raw124_unique_membership_in_canonical58"]
    assert report["raw124_parent_artifact_id"] == RAW124_PARENT_ARTIFACT_ID
    assert report["raw124_parent_artifact_sha256"] == RAW124_PARENT_ARTIFACT_SHA
    assert report["raw124_parent_weighted_bound"] == 4136175
    assert report["canonical58_olean_sha256"] == a68.sha(
        linked / "Canonical58Raw113Graft.olean"
    )
    assert report["graft_olean_sha256"] == a68.sha(
        linked / "Raw124Canonical58Membership.olean"
    )
    assert report["raw124_parent_olean_sha256"] == a68.sha(
        linked / "Raw124ParentComplete.olean"
    )
    return linked, item, report_path, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical57-run-id", type=int, default=BASE_RUN)
    parser.add_argument("--raw59-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    linked, base_artifact, base_report_path, base_report = verify_base(
        work, args.canonical57_run_id
    )

    # Reuse the existing Raw59 slice consumer. It checks the staged artifact's
    # accepted theorem, verifies its digest, and audits every reachable
    # duplicate object by exact bytes or kernel equality.
    raw59_delta = raw59.add_raw59(work, linked, args.raw59_run_id)
    env = dict(os.environ, LEAN_PATH=str(linked))

    source = HERE / "Raw59Canonical56AfterRaw124.lean"
    output = linked / f"{source.stem}.olean"
    assert not output.exists(), output
    log = a68.compile_module(
        source, output, env, work / "canonical56-raw59-after-raw124.log"
    )
    profiles = a68.gate(log, [NS + "." + name for name in (
        "p59_count57", "p59_count56", "count56", "raw113_removed",
        "raw124_removed", "parents_pairwise_distinct", "parents_root",
        "parents_cover", "sound_integrated", "exact_at_target",
        "exact_at_champion_score",
    )])

    generated = work / "generated"
    generated.mkdir(exist_ok=True)
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / base_report_path.name)
    report = {
        "status": "source-accepted Canonical57-Raw124 to Canonical56-Raw59 graft",
        "canonical57_run_id": args.canonical57_run_id,
        "canonical57_artifact_name": base_artifact["name"],
        "canonical57_artifact_id": base_artifact["id"],
        "canonical57_artifact_sha256": BASE_ARTIFACT_SHA,
        "canonical57_source_revision": base_report["canonical58_source_revision"],
        "canonical57_residual_count": 57,
        "canonical58_residual_count": 58,
        "canonical58_base_run_id": base_report["canonical58_base_run_id"],
        "canonical58_artifact_sha256": base_report["canonical58_artifact_sha256"],
        "canonical58_olean_sha256": base_report["canonical58_olean_sha256"],
        "raw113_consumed": True,
        "raw124_consumed": True,
        "raw124_parent_run_id": RAW124_PARENT_RUN,
        "raw124_parent_artifact_id": RAW124_PARENT_ARTIFACT_ID,
        "raw124_parent_artifact_sha256": RAW124_PARENT_ARTIFACT_SHA,
        "raw124_parent_weighted_bound": 4136175,
        "raw59_run_id": args.raw59_run_id,
        "raw59": raw59_delta,
        "raw59_consumed": True,
        "raw113_removed": True,
        "raw124_removed": True,
        "remaining_residual_count": 56,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    report_path = work / "canonical56-raw59-after-raw124.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
