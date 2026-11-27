#!/usr/bin/env python3
"""Directly remove eight source-accepted parents from accepted Canonical58."""

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
sys.path.insert(0, str(ROOT / "im-results" / "agent2-tnf-raw124"))

import assemble_canonical53_from58 as five
import assemble_canonical55 as c55
import assemble_canonical53 as c53
import assemble_canonical68 as a68
import assemble_canonical59_five_parent as five_parent
import assemble_canonical_selected as selected
import assemble_raw124_canonical57 as raw124

REPO = "FlareZ123/bb6"
NS = "BB6.Agent31Canonical50EightReadyParents"

LEGACY = {
    "69": {
        "label": "raw69",
        "run_id": 45585422842,
        "revision": "748b52c544dec5d432888f59afbdcb15a68b37d9",
        "artifact_id": 15007309346,
        "artifact_name": "raw69-bound-certified",
        "digest": "59ed35c0a1477fd402efc26c36a04d5bbf73d33558a9e2985525c836ce405023",
        "size": 13731429,
        "root": "Raw69Bound",
        "theorem": "BB6.Agent21Raw69.all_completions",
        "bound": 7014,
    },
    "73": {
        "label": "raw73",
        "run_id": 45584889944,
        "revision": "6b646833d5796ba29c9bca26efbfec8df3e729f0",
        "artifact_id": 15008541852,
        "artifact_name": "raw73-bound-certified",
        "digest": "3bf907a782e40c0b914efd61c678c29fedd86ee0d270a91a8c0b93534ac913fb",
        "size": 12195179,
        "root": "Raw73Bound",
        "theorem": "BB6.Agent21Raw73.all_completions",
        "bound": 7014,
    },
    "78": {
        "label": "raw78",
        "run_id": 45585432166,
        "revision": "748b52c544dec5d432888f59afbdcb15a68b37d9",
        "artifact_id": 15007424155,
        "artifact_name": "raw78-bound-certified",
        "digest": "81aa9e8207e73eb71ed0afcfc5a40a68ef6295f4f22941efcffc7c75bc5b5c87",
        "size": 15370372,
        "root": "Raw78Bound",
        "theorem": "BB6.Agent21Raw78.all_completions",
        "bound": 7014,
    },
}


def verify_legacy(raw: str, work: Path):
    spec = LEGACY[raw]
    run = a68.api_json(f"repos/{REPO}/actions/runs/{spec['run_id']}")
    assert run["conclusion"] == "success", run.get("conclusion")
    assert run["head_sha"] == spec["revision"], (run["head_sha"], spec["revision"])

    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{spec['run_id']}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["id"] == spec["artifact_id"]]
    assert len(matches) == 1, matches
    item = matches[0]
    assert item["name"] == spec["artifact_name"], item["name"]
    assert item["digest"] == "sha256:" + spec["digest"], item["digest"]
    assert item["size_in_bytes"] == spec["size"], item["size_in_bytes"]
    assert not item["expired"]

    dirs = a68.download(
        (spec["artifact_id"], spec["run_id"], spec["digest"]), work
    )
    roots = [
        p for p in work.rglob(spec["root"] + ".olean")
        if "metadata" not in p.parts
    ]
    assert len(roots) == 1, [str(p) for p in roots]

    manifests = [
        p for p in work.rglob("manifest.json")
        if "metadata" not in p.parts
    ]
    assert len(manifests) == 1, [str(p) for p in manifests]
    manifest_path = manifests[0]
    manifest = json.loads(manifest_path.read_text())
    assert manifest["proof_source_revision"] == spec["revision"]
    assert "4.36.0-rc2" in manifest["lean_version"]
    assert manifest["artifact_name"] == spec["artifact_name"]
    assert manifest["claim"]["theorem"] == spec["theorem"]
    assert manifest["claim"]["weighted_bound"] == spec["bound"]
    assert manifest["workflow"]["run_id"] == str(spec["run_id"])
    assert any(x["module"] == spec["root"] for x in manifest["roots"])
    module = next(x for x in manifest["modules"] if x["module"] == spec["root"])
    assert module["olean_sha256"] == a68.sha(roots[0])
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert manifest["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")
    return dirs, item, manifest_path, manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    names = ["base", "raw124", "raw106", "raw79", "raw83", "raw85",
             "raw69", "raw73", "raw78"]
    dirs_work = {name: work / name for name in names}
    for d in dirs_work.values():
        d.mkdir()

    linked, base_item, base_report_path, base_report = five.verify_base(dirs_work["base"])

    raw124_item, raw124_dirs, raw124_manifest_path, raw124_manifest = (
        raw124.verify_raw124_parent(raw124.RAW124_RUN, dirs_work["raw124"])
    )

    family_inputs = [
        ({"label": "raw124", "root": "Raw124ParentComplete"}, raw124_dirs),
    ]
    metadata_paths = {
        "raw124": raw124_manifest_path,
    }

    for raw in ("106", "79"):
        parent_dirs, report_path, report = c55.verify_parent(
            raw, dirs_work["raw" + raw]
        )
        family_inputs.append((c55.PARENTS[raw], parent_dirs))
        metadata_paths["raw" + raw] = report_path

    raw83_dirs, raw83_metadata = five_parent.download_parent(
        c53.RAW83, dirs_work["raw83"]
    )
    family_inputs.append((c53.RAW83, raw83_dirs))

    raw85_dirs, raw85_manifest_path, raw85_manifest = c53.verify_raw85(
        dirs_work["raw85"]
    )
    family_inputs.append((c53.RAW85, raw85_dirs))
    metadata_paths["raw85"] = raw85_manifest_path

    legacy_manifests = {}
    for raw in ("69", "73", "78"):
        parent_dirs, item, manifest_path, manifest = verify_legacy(
            raw, dirs_work["raw" + raw]
        )
        family_inputs.append((LEGACY[raw], parent_dirs))
        legacy_manifests[raw] = {
            "artifact_id": item["id"],
            "manifest_path": manifest_path,
            "manifest": manifest,
        }
        metadata_paths["raw" + raw] = manifest_path

    copied = []
    link_audits = {}
    for spec, parent_dirs in family_inputs:
        audit = {}
        selected.add_family(spec, parent_dirs, linked, copied, audit)
        link_audits[spec["label"]] = audit

    source = HERE / "Canonical50EightReadyParentsGraft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(
        source, output, env, work / "canonical50-eight-ready-parents.log"
    )

    required = [
        NS + "." + name for name in (
            "p124_count58", "p106_count58", "p79_count58", "p83_count58",
            "p85_count58", "p69_count58", "p73_count58", "p78_count58",
            "parents_pairwise_distinct",
            "p124_cover", "p106_cover", "p79_cover", "p83_cover",
            "p85_cover", "p69_cover", "p73_cover", "p78_cover",
            "count50", "all_ready_parents_removed", "raw59_retained",
            "sound_integrated", "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical58-base-report.json")
    for label, path in metadata_paths.items():
        shutil.copy2(path, generated / (label + "-metadata.json"))
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(c53.RAW83, indent=2, sort_keys=True) + "\n"
    )

    report = {
        "status": "source-accepted direct Canonical58-to-50 eight-ready-parent delta",
        "lean_version": lean_version,
        "canonical58_run_id": five.BASE_RUN,
        "canonical58_artifact_id": five.BASE_ARTIFACT_ID,
        "canonical58_artifact_name": base_item["name"],
        "canonical58_artifact_sha256": five.BASE_ARTIFACT_SHA,
        "canonical58_source_revision": five.BASE_SOURCE_REVISION,
        "canonical58_residual_count": 58,
        "canonical58_olean_sha256": base_report["olean_sha256"],
        "parents": {
            "raw124": {
                "run_id": raw124.RAW124_RUN,
                "artifact_id": raw124_item["id"],
                "bound": raw124.RAW124_BOUND,
            },
            "raw106": {**c55.PARENTS["106"], "run_id": c55.PARENT_RUN},
            "raw79": {**c55.PARENTS["79"], "run_id": c55.PARENT_RUN},
            "raw83": {**c53.RAW83, "metadata": raw83_metadata},
            "raw85": c53.RAW85,
            **{
                "raw" + raw: {
                    **LEGACY[raw],
                    "manifest_sha256": a68.sha(legacy_manifests[raw]["manifest_path"]),
                }
                for raw in ("69", "73", "78")
            },
        },
        "link_audits": link_audits,
        "all_eight_unique_membership_in_canonical58": True,
        "all_eight_pairwise_distinct": True,
        "raw59_retained": True,
        "remaining_residual_count": 50,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical50-eight-ready-parents.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
