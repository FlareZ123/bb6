#!/usr/bin/env python3
"""Consume the staged Raw59 Cover after the accepted Raw124 Canonical57 graft."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))

import assemble_canonical68 as a68
import assemble_canonical59_raw59_graft as raw59
import assemble_raw124_canonical57 as raw124

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
RAW124_DELTA_RUN = 45926694578
RAW124_DELTA_ID = 15167645810
RAW124_DELTA_SHA = "de6fb52e65ec6ce4ba06cfee40f74572d9f99444c10bc1493ea44cc86b34939a"
RAW124_DELTA_REVISION = "7b009ba1127836b2e1d318e458632ea06bccbed0"


def restore_raw124_delta(work, linked, base_item):
    """Restore the exact previously accepted Raw124 edge, without recompilation.

    The earlier overall run failed only in its subsequent Raw59 step. Its
    independently uploaded, pinned delta is accepted. Reuse the old kernel
    equality verdicts only for byte-identical pairs of objects.
    """
    run = a68.api_json(f"repos/{REPO}/actions/runs/{RAW124_DELTA_RUN}")
    assert run["head_sha"] == RAW124_DELTA_REVISION
    info = a68.api_json(f"repos/{REPO}/actions/artifacts/{RAW124_DELTA_ID}")
    assert info["workflow_run"]["id"] == RAW124_DELTA_RUN
    assert info["name"] == "canonical57-raw124-thin-delta" and not info["expired"]
    assert info["digest"] == "sha256:" + RAW124_DELTA_SHA
    archive = work / f"{RAW124_DELTA_ID}.zip"
    with archive.open("wb") as stream:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{RAW124_DELTA_ID}/zip"],
                       stdout=stream, check=True)
    assert a68.sha(archive) == RAW124_DELTA_SHA
    delta = work / "raw124-delta"
    delta.mkdir()
    names = {"delta.json", "raw124-canonical58-membership.json",
             "Raw124Canonical58Membership.lean", "Raw124Canonical58Membership.olean"}
    with zipfile.ZipFile(archive) as z:
        entries = [i for i in z.infolist() if not i.is_dir()]
        assert len(entries) == len(names)
        assert {Path(i.filename).name for i in entries} == names
        for i in entries:
            (delta / Path(i.filename).name).write_bytes(z.read(i))
    archive.unlink()
    manifest = json.loads((delta / "delta.json").read_text())
    report_path = delta / "raw124-canonical58-membership.json"
    report = json.loads(report_path.read_text())
    root = delta / "Raw124Canonical58Membership.olean"
    source = delta / "Raw124Canonical58Membership.lean"
    assert manifest["status"] == "source-accepted Canonical58-to-57 Raw124 thin delta"
    assert manifest["source_revision"] == RAW124_DELTA_REVISION
    assert manifest["base_run_id"] == BASE_RUN and manifest["base_artifact_id"] == base_item["id"]
    assert manifest["base_artifact_sha256"] == BASE_ARTIFACT_SHA
    assert manifest["base_source_revision"] == BASE_SOURCE_REVISION
    assert manifest["base_root_sha256"] == a68.sha(linked / "Canonical58Raw113Graft.olean")
    assert manifest["parent_run_id"] == RAW124_PARENT_RUN
    assert manifest["parent_artifact_id"] == RAW124_PARENT_ARTIFACT_ID
    assert manifest["parent_artifact_sha256"] == RAW124_PARENT_ARTIFACT_SHA
    assert manifest["remaining_residual_count"] == 57
    assert manifest["report_sha256"] == a68.sha(report_path)
    assert manifest["graft_root_sha256"] == report["graft_olean_sha256"] == a68.sha(root)
    assert manifest["graft_source_sha256"] == report["graft_source_sha256"] == a68.sha(source)
    assert manifest["axioms"] == report["axioms"]
    assert all(set(v) <= {"propext", "Classical.choice", "Quot.sound"}
               for v in report["axioms"].values())
    required = ("p124_count64", "p124_count58", "p124_root", "p124_cover", "count57",
                "sound_integrated", "exact_at_target", "exact_at_champion_score")
    assert all("BB6.Agent2Raw124Canonical58Membership." + n in report["axioms"] for n in required)

    parent_work = work.parent / "raw124-parent-artifact"
    parent_work.mkdir(exist_ok=False)
    _, dirs, parent_manifest_path, parent_manifest = raw124.verify_raw124_parent(
        RAW124_PARENT_RUN, parent_work)
    assert a68.sha(parent_manifest_path) == report["raw124_parent_manifest_sha256"]
    assert parent_manifest["objects"]["Raw124ParentComplete.olean"] == report["raw124_parent_olean_sha256"]
    audit = report["parent_link_audit"]
    collisions = {x["module"]: x for x in audit["collisions"]}
    assert len(collisions) == len(audit["collisions"])
    observed = set()
    modules = set()
    for obj in audit["objects"]:
        name, digest = obj["module"], obj["sha256"]
        assert name == Path(name).name and name.endswith(".olean") and name not in modules
        modules.add(name)
        hits = [d / name for d in dirs if (d / name).is_file()]
        assert len(hits) == 1 and a68.sha(hits[0]) == digest, name
        dest = linked / name
        if dest.is_file():
            chosen = a68.sha(dest)
            if chosen != digest:
                prior = collisions[name]
                assert prior["equal"] and prior["chosen"] == chosen and prior["other"] == digest
                observed.add(name)
        else:
            assert name not in collisions
            shutil.copy2(hits[0], dest)
    assert observed == set(collisions)
    assert "Raw124ParentComplete.olean" in modules
    assert a68.sha(linked / "Raw124ParentComplete.olean") == report["raw124_parent_olean_sha256"]
    shutil.rmtree(parent_work)
    shutil.copy2(root, linked / root.name)
    result = work / report_path.name
    shutil.copy2(report_path, result)
    print(f"Restored accepted Raw124 delta {RAW124_DELTA_ID} ({len(modules)} parent objects)", flush=True)
    return result


def verify_base(work: Path, run_id: int, resume: bool = False):
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

    dirs = ([p.parent for p in work.rglob("Canonical58Raw113Graft.olean")]
            if resume else a68.download((item["id"], run_id, BASE_ARTIFACT_SHA), work))
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
    if resume:
        reports57 = [work / "raw124-canonical58-membership.json"]
        assert graft.is_file() and reports57[0].is_file()
    if not graft.exists():
        assert not reports57, [str(p) for p in reports57]
        report_path = restore_raw124_delta(work, linked, item)
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


def export_raw124_delta(work, linked, base_artifact, report_path, report):
    """Preserve the independently checked Raw124 root and its reconstruction inputs."""
    delta = work / "raw124-delta"
    delta.mkdir()
    root = linked / "Raw124Canonical58Membership.olean"
    source = HERE / "Raw124Canonical58Membership.lean"
    assert a68.sha(source) == report["graft_source_sha256"]
    shutil.copy2(root, delta / root.name)
    shutil.copy2(source, delta / source.name)
    shutil.copy2(report_path, delta / report_path.name)
    manifest = {
        "status": "source-accepted Canonical58-to-57 Raw124 thin delta",
        "base_run_id": BASE_RUN,
        "base_artifact_id": base_artifact["id"],
        "base_artifact_sha256": BASE_ARTIFACT_SHA,
        "base_source_revision": BASE_SOURCE_REVISION,
        "base_root_sha256": report["canonical58_olean_sha256"],
        "parent_run_id": RAW124_PARENT_RUN,
        "parent_artifact_id": RAW124_PARENT_ARTIFACT_ID,
        "parent_artifact_sha256": RAW124_PARENT_ARTIFACT_SHA,
        "graft_root_sha256": a68.sha(root),
        "graft_source_sha256": a68.sha(source),
        "report_sha256": a68.sha(report_path),
        "remaining_residual_count": 57,
        "axioms": report["axioms"],
        "replay_recipe": "Link the pinned Canonical58 and Raw124 parent artifacts "
                         "with assemble_raw124_canonical57.py and compare "
                         "parent_link_audit and graft hashes to the report.",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip(),
    }
    (delta / "delta.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical57-run-id", type=int, default=BASE_RUN)
    parser.add_argument("--raw59-run-id", type=int)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--resume", action="store_true")
    args = parser.parse_args()

    work = args.work.resolve()
    if not args.prepare_only and args.raw59_run_id is None:
        parser.error("--raw59-run-id is required except with --prepare-only")
    if not args.resume:
        work.mkdir(parents=True, exist_ok=False)
    linked, base_artifact, base_report_path, base_report = verify_base(
        work, args.canonical57_run_id, resume=args.resume
    )
    if args.resume:
        manifest = json.loads((work / "raw124-delta/delta.json").read_text())
        assert manifest["graft_root_sha256"] == base_report["graft_olean_sha256"]
        assert manifest["report_sha256"] == a68.sha(base_report_path)
    elif not (work / "raw124-delta").is_dir():
        export_raw124_delta(work, linked, base_artifact, base_report_path, base_report)
    if args.prepare_only:
        return

    # Reuse the existing Raw59 slice consumer. It checks the staged artifact's
    # accepted theorem, verifies its digest, and audits every reachable
    # duplicate object by exact bytes or kernel equality.
    raw59_delta = raw59.add_raw59(work, linked, args.raw59_run_id, parent_only=True)
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
        "p59_source_eq", "p59_cover", "parents_cover", "sound_integrated", "exact_at_target",
        "exact_at_champion_score",
    )])

    generated = work / "generated"
    generated.mkdir(exist_ok=True)
    shutil.copy2(source, generated / source.name)
    report = {
        "status": "source-accepted Canonical57-Raw124 to Canonical56-Raw59 graft",
        "canonical57_run_id": args.canonical57_run_id,
        "canonical57_artifact_name": base_artifact["name"],
        "canonical57_artifact_id": base_artifact["id"],
        "canonical57_artifact_sha256": BASE_ARTIFACT_SHA,
        "canonical57_source_revision": base_report["canonical58_source_revision"],
        "canonical57_residual_count": 57,
        "canonical57_raw124_delta_artifact_id": RAW124_DELTA_ID,
        "canonical57_raw124_delta_sha256": RAW124_DELTA_SHA,
        "canonical57_raw124_root_sha256": base_report["graft_olean_sha256"],
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
    # Publish the new consumer as a thin delta. The authenticated predecessor
    # artifacts already carry its exact reachable dependencies; publishing
    # another multi-GB copy of those objects would delay acceptance.
    delta = work / "raw59-delta"
    delta.mkdir()
    for path in (source, output, report_path, work / "raw59-link-audit.json"):
        shutil.copy2(path, delta / path.name)
    shutil.copy2(work / "raw124-delta/delta.json", delta / "raw124-delta.json")
    manifest = {
        "status": "source-accepted Canonical57-Raw124 to Canonical56-Raw59 thin delta",
        "remaining_residual_count": 56,
        "base_delta_artifact_id": RAW124_DELTA_ID,
        "base_delta_artifact_sha256": RAW124_DELTA_SHA,
        "base_delta_root_sha256": base_report["graft_olean_sha256"],
        "raw59_staged_artifact_id": raw59_delta["artifact_id"],
        "raw59_staged_artifact_sha256": raw59_delta["artifact_sha256"],
        "raw59_link_audit_sha256": raw59_delta["link_audit_sha256"],
        "raw59_linked_root": raw59_delta["linked_root"],
        "raw59_slice_root_sha256": raw59_delta["slice_olean_sha256"],
        "graft_root_sha256": a68.sha(output),
        "graft_source_sha256": a68.sha(source),
        "report_sha256": a68.sha(report_path),
        "axioms": profiles,
        "source_revision": report["source_revision"],
        "replay_recipe": "Restore the pinned Raw124 delta, link only Raw59KernelSlice "
                         "from the pinned staged artifact using the saved link audit, "
                         "and install the checked Raw59Canonical56AfterRaw124 root.",
    }
    (delta / "delta.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
