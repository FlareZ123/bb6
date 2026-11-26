#!/usr/bin/env python3
"""Link the accepted Raw124 parent Cover into the accepted Canonical58 closure."""
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
import assemble_canonical_selected as selected

REPO = "FlareZ123/bb6"
RAW124_RUN = 45908591612
RAW124_SOURCE_REVISION = "40f4a850b46aef1e0fd840d2a56f9df8c0965bdd"
RAW124_ARTIFACT = "raw124-complete-parent-proof"
RAW124_ARTIFACT_ID = 15159377345
RAW124_ARTIFACT_SHA = "9ec5b5b86fe4f78d636fd9a37891cabdd0017c04c8fc62f74f4ef6022ffcfa15"
RAW124_ARTIFACT_SIZE = 1016135019
RAW124_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LF_------"
RAW124_BOUND = 4136175
NS = "BB6.Agent2Raw124Canonical58Membership"


def verify_raw124_parent(run_id: int, work: Path):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", (run_id, run.get("conclusion"))
    assert run["head_sha"] == RAW124_SOURCE_REVISION, (run["head_sha"], RAW124_SOURCE_REVISION)
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    matches = [item for item in artifacts if item["name"] == RAW124_ARTIFACT]
    assert len(matches) == 1, [(item["id"], item["name"]) for item in artifacts]
    item = matches[0]
    assert item["id"] == RAW124_ARTIFACT_ID, item["id"]
    assert item["size_in_bytes"] == RAW124_ARTIFACT_SIZE, item["size_in_bytes"]
    assert item["digest"] == "sha256:" + RAW124_ARTIFACT_SHA, item["digest"]
    assert not item["expired"], item["id"]

    dirs = a68.download((item["id"], run_id, RAW124_ARTIFACT_SHA), work)
    roots = [directory for directory in dirs
             if (directory / "Raw124ParentComplete.olean").is_file()]
    assert len(roots) == 1, [str(directory) for directory in dirs]

    metadata_dir = work / "metadata" / str(item["id"])
    manifests = list(metadata_dir.rglob("manifest.json"))
    assert len(manifests) == 1, [str(path) for path in manifests]
    manifest_path = manifests[0]
    manifest = json.loads(manifest_path.read_text())
    claim = manifest["claim"]
    assert claim["theorem"] == "BB6.Agent2Raw124ParentComplete.parent_cover", claim
    assert claim["parent_table"] == RAW124_TABLE, claim
    assert claim["weighted_bound"] == RAW124_BOUND, claim
    assert manifest["proof_source_revision"] == run["head_sha"]
    assert "4.36.0-rc2" in manifest["lean_version"], manifest["lean_version"]
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert manifest["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")
    assert manifest["objects"]["Raw124ParentComplete.olean"] == a68.sha(
        roots[0] / "Raw124ParentComplete.olean"
    )
    axiom_log = manifest["axiom_log"]
    assert "sorryAx" not in axiom_log and "native_decide" not in axiom_log
    return item, roots, manifest_path, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--raw124-run-id", type=int, default=RAW124_RUN)
    args = parser.parse_args()

    work = args.work.resolve()
    graft_reports = list(work.glob("canonical58-raw113-graft.json"))
    assert len(graft_reports) == 1, [str(path) for path in graft_reports]
    base_report = json.loads(graft_reports[0].read_text())
    assert base_report["remaining_residual_count"] == 58, base_report
    assert base_report["raw59_retained"], base_report
    assert "raw118" in base_report["base_accepted"], base_report["base_accepted"]
    assert base_report["axioms"], base_report

    roots = list(work.rglob("Canonical58Raw113Graft.olean"))
    roots = [path for path in roots if "metadata" not in path.parts]
    assert len(roots) == 1, [str(path) for path in roots]
    linked = roots[0].parent

    # Keep the downloaded 1 GB parent artifact outside the Canonical58
    # artifact staging directory; only its exact reachable closure is linked.
    parent_work = work.parent / "raw124-parent-artifact"
    parent_work.mkdir(exist_ok=True)
    item, parent_dirs, manifest_path, parent_manifest = verify_raw124_parent(
        args.raw124_run_id, parent_work
    )

    copied = []
    link_audit = {}
    selected.add_family(
        {"root": "Raw124ParentComplete"}, parent_dirs, linked, copied, link_audit
    )
    assert (linked / "Raw124ParentComplete.olean").is_file()

    source = HERE / "Raw124Canonical58Membership.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log_path = work / "raw124-canonical58-membership.log"
    log = a68.compile_module(source, output, env, log_path)
    profiles = a68.gate(log, [
        NS + ".p124_count64",
        NS + ".p124_count58",
        NS + ".p124_root",
        NS + ".p124_cover",
        NS + ".count57",
        NS + ".sound_integrated",
        NS + ".exact_at_target",
        NS + ".exact_at_champion_score",
    ])

    generated = work / "generated"
    generated.mkdir(exist_ok=True)
    shutil.copy2(source, generated / source.name)
    report = {
        "status": "source-accepted Canonical58-to-57 Raw124 delta",
        "canonical58_workflow_run_id": os.environ.get("GITHUB_RUN_ID"),
        "canonical58_source_revision": base_report["source_revision"],
        "canonical58_base_run_id": base_report["base_run_id"],
        "canonical58_artifact_sha256": base_report["base_artifact_sha256"],
        "canonical58_olean_sha256": base_report["olean_sha256"],
        "canonical58_residual_count": 58,
        "raw124_parent_run_id": args.raw124_run_id,
        "raw124_parent_artifact_id": item["id"],
        "raw124_parent_artifact_name": item["name"],
        "raw124_parent_artifact_sha256": RAW124_ARTIFACT_SHA,
        "raw124_parent_manifest_sha256": a68.sha(manifest_path),
        "raw124_parent_source_revision": parent_manifest["proof_source_revision"],
        "raw124_parent_theorem": "BB6.Agent2Raw124ParentComplete.parent_cover",
        "raw124_parent_table": RAW124_TABLE,
        "raw124_parent_weighted_bound": RAW124_BOUND,
        "raw124_parent_olean_sha256": parent_manifest["objects"]["Raw124ParentComplete.olean"],
        "raw124_unique_membership_in_canonical58": True,
        "canonical57_residual_count": 57,
        "raw59_retained": base_report["raw59_retained"],
        "raw118_absent": "raw118" in base_report["base_accepted"],
        "raw124_removed": True,
        "graft_source": str(source.relative_to(ROOT)),
        "graft_source_sha256": a68.sha(source),
        "graft_olean_sha256": a68.sha(output),
        "axioms": profiles,
        "parent_link_audit": link_audit,
    }
    report_path = work / "raw124-canonical58-membership.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
