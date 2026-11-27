#!/usr/bin/env python3
"""Graft the already accepted sharp Raw122 parent onto the actual Canonical57."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent2-tnf-raw124"))
import assemble_raw59_canonical56_after_raw124 as base57
import assemble_canonical68 as a68
import assemble_canonical_selected as selected

RUN = 45866162212
REV = "51fc0fa0dc4e1f5c9a62451c42d9431ad19951a7"
ARTIFACT = 15143745937
SHA = "b225a97ac16a238cde12205f962389eca4ed12a415a713481a99f6a5b4f5c2be"
TABLE = "1RB---_1RC---_0RD---_1LD1RE_---0LF_------"
ROOT = "Raw122SharpParent"
NS = "BB6.Agent43Raw122Canonical57Graft"

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    linked, base_artifact, _, base_report = base57.verify_base(work, base57.BASE_RUN)
    run = a68.api_json(f"repos/{base57.REPO}/actions/runs/{RUN}")
    assert run["conclusion"] == "success" and run["head_sha"] == REV
    item = a68.api_json(f"repos/{base57.REPO}/actions/artifacts/{ARTIFACT}")
    assert item["workflow_run"]["id"] == RUN
    assert item["name"] == "raw122-sharp-parent" and not item["expired"]
    assert item["size_in_bytes"] == 1714262249
    assert item["digest"] == "sha256:" + SHA
    parent_work = work / "raw122-parent"
    parent_work.mkdir()
    dirs = a68.download((ARTIFACT, RUN, SHA), parent_work)
    manifest_path, = (parent_work / "metadata").rglob("manifest.json")
    manifest = json.loads(manifest_path.read_text())
    assert manifest["proof_source_revision"] == REV
    assert manifest["claim"] == {"theorem": "BB6.Agent43Raw122SharpParent.parent_bound",
                                  "parent_table": TABLE, "weighted_bound": 6659487}
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert manifest["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")
    modules = {m["module"]: m["olean_sha256"] for m in manifest["modules"]}
    assert len(modules) == manifest["module_count"]
    root, = [p / (ROOT + ".olean") for p in dirs if (p / (ROOT + ".olean")).is_file()]
    assert a68.sha(root) == modules[ROOT]
    audit = {}
    try:
        selected.add_family({"root": ROOT}, dirs, linked, [], audit)
    finally:
        (work / "raw122-link-audit.json").write_text(json.dumps(audit, indent=2) + "\n")
    for obj in audit["objects"]:
        assert obj["sha256"] == modules[Path(obj["module"]).stem], obj
    source = HERE / "Raw122Canonical57Graft.lean"
    out = linked / "Raw122Canonical57Graft.olean"
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(source, out, env, work / "raw122-graft.log")
    names = ["p122_count64", "p122_count57", "p122_root", "p122_cover", "count56",
             "p122_count56", "raw59_retained", "raw113_absent", "raw124_absent",
             "sound_integrated", "exact_at_target", "exact_at_champion_score"]
    axioms = a68.gate(log, [NS + "." + n for n in names])
    assert not any(bad in log for bad in ("sorryAx", "native_decide", "Lean.ofReduceBool"))
    delta = work / "raw122-delta"
    delta.mkdir()
    shutil.copy2(source, delta)
    shutil.copy2(out, delta)
    shutil.copy2(work / "raw122-link-audit.json", delta)
    shutil.copy2(manifest_path, delta / "parent-manifest.json")
    shutil.copy2(work / "raw124-canonical58-membership.json", delta / "base57-report.json") if (work / "raw124-canonical58-membership.json").exists() else (delta / "base57-report.json").write_text(json.dumps(base_report, indent=2) + "\n")
    report = {"status": "source-accepted Canonical57-to-56 Raw122 thin delta",
              "source_revision": os.environ["GITHUB_SHA"], "run_id": os.environ["GITHUB_RUN_ID"],
              "base_run_id": base57.BASE_RUN, "base_artifact_id": base_artifact["id"],
              "base_artifact_sha256": base57.BASE_ARTIFACT_SHA,
              "base57_delta_artifact_id": base57.RAW124_DELTA_ID,
              "base57_delta_sha256": base57.RAW124_DELTA_SHA,
              "base57_root_sha256": base_report["graft_olean_sha256"],
              "parent_run_id": RUN, "parent_artifact_id": ARTIFACT, "parent_artifact_sha256": SHA,
              "parent_root_sha256": modules[ROOT], "parent_manifest_sha256": a68.sha(manifest_path),
              "parent_table": TABLE, "parent_weighted_bound": 6659487,
              "remaining_residual_count": 56, "raw59_retained": True,
              "graft_root_sha256": a68.sha(out), "graft_source_sha256": a68.sha(source),
              "axioms": axioms}
    (delta / "delta.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2), flush=True)

if __name__ == "__main__":
    main()
