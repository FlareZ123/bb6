#!/usr/bin/env python3
"""Compose disjoint accepted parent Covers on the actual Canonical57 lineage."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
for sibling in ("agent2-tnf-raw124", "agent31-shared-core",
                "agent31-raw106-79-canonical55", "agent32-four-sharp"):
    sys.path.insert(0, str(HERE.parent / sibling))

import assemble_raw59_canonical56_after_raw124 as base
import assemble_canonical54 as sharp
import assemble_canonical50_from58 as ready
import assemble_canonical55 as c55
import assemble_canonical53 as c53
import assemble_canonical59_five_parent as five_parent
import assemble_canonical68 as a68
import assemble_canonical_selected as selected


def compile_one(source, linked, evidence, names):
    output = linked / (source.stem + ".olean")
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(source, output, env, evidence / (source.stem + ".log"))
    profiles = selected.gate(log, names)
    shutil.copy2(source, evidence / source.name)
    return output, profiles


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--phase", choices=("sharp", "ready"), required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    stage = args.phase
    if stage == "sharp":
        work.mkdir(parents=True, exist_ok=False)
    delta = work / (stage + "-delta")
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()
    inputs = work / (stage + "-inputs")
    inputs.mkdir()
    families = []
    parents = {}
    def folder(raw):
        path = inputs / ("raw" + raw)
        path.mkdir()
        return path
    if stage == "sharp":
        for raw, spec in sharp.SPECS.items():
            dirs, manifest = sharp.verify_parent(spec, folder(raw))
            families.append((spec, dirs))
            parents[spec["label"]] = spec
            shutil.copy2(manifest, evidence / ("raw" + raw + "-manifest.json"))
    else:
        for raw in ("106", "79"):
            dirs, report_path, report = c55.verify_parent(raw, folder(raw))
            spec = c55.PARENTS[raw]
            families.append((spec, dirs))
            parents[spec["label"]] = dict(spec, run_id=c55.PARENT_RUN)
            shutil.copy2(report_path, evidence / ("raw" + raw + "-manifest.json"))
        dirs, meta = five_parent.download_parent(c53.RAW83, folder("83"))
        families.append((c53.RAW83, dirs))
        parents["raw83"] = dict(c53.RAW83, metadata=meta)
        dirs, path, manifest = c53.verify_raw85(folder("85"))
        families.append((c53.RAW85, dirs))
        parents["raw85"] = c53.RAW85
        shutil.copy2(path, evidence / "raw85-manifest.json")
        for raw in ("69", "73", "78"):
            dirs, item, path, manifest = ready.verify_legacy(raw, folder(raw))
            spec = ready.LEGACY[raw]
            families.append((spec, dirs))
            parents[spec["label"]] = spec
            shutil.copy2(path, evidence / ("raw" + raw + "-manifest.json"))

    linked, item, report_path, base_report = base.verify_base(
        work, base.BASE_RUN, resume=(stage == "ready"))
    if stage == "sharp":
        # The resume path expects the restored report at work root.
        assert (work / "raw124-delta/delta.json").is_file()
        previous_hash = base_report["graft_olean_sha256"]
    else:
        prior = json.loads((work / "sharp-delta/delta.json").read_text())
        assert prior["remaining_residual_count"] == 53
        for name, digest in prior["delta_objects"].items():
            assert a68.sha(linked / name) == digest
        previous_hash = prior["root_sha256"]
    copied = []
    audits = {}
    for spec, dirs in families:
        audit = {}
        selected.add_family(spec, dirs, linked, copied, audit)
        audits[spec["label"]] = audit

    profiles = {}
    if stage == "sharp":
        root, ax = compile_one(sharp.HERE / "FourSharpCover.lean", linked, evidence,
            ["BB6.Agent32FourSharp.parent_covers", "BB6.Agent32FourSharp.union_exact"])
        copied.append(root)
        profiles.update(ax)
        source = HERE / "Canonical53FourSharpAfterRaw124.lean"
        ns = "BB6.Agent2Canonical53FourSharp"
        names = ["unique_membership", "pairwise_distinct", "parents_root",
                 "parents_cover", "count53", "all_removed", "raw59_retained"]
        remaining = 53
    else:
        source = HERE / "Canonical46SevenReadyAfterSharp.lean"
        ns = "BB6.Agent2Canonical46SevenReady"
        raw_ids = ("106", "79", "83", "85", "69", "73", "78")
        names = ["p" + raw + "_count53" for raw in raw_ids]
        names += ["p" + raw + "_cover" for raw in raw_ids]
        names += ["parents_pairwise_distinct", "count46",
                  "all_ready_parents_removed", "raw59_retained"]
        remaining = 46
    names += ["sound_integrated", "exact_at_target", "exact_at_champion_score"]
    root, ax = compile_one(source, linked, evidence, [ns + "." + n for n in names])
    copied.append(root)
    profiles.update(ax)
    hashes = {}
    for path in copied:
        target = objects / path.name
        assert not target.exists(), target
        shutil.copy2(path, target)
        hashes[path.name] = a68.sha(target)
    report = {
        "status": "source-accepted canonical parent-union thin delta",
        "base_artifact_id": base.BASE_ARTIFACT_ID,
        "base_artifact_sha256": base.BASE_ARTIFACT_SHA,
        "raw124_delta_artifact_id": base.RAW124_DELTA_ID,
        "raw124_delta_sha256": base.RAW124_DELTA_SHA,
        "previous_root_sha256": previous_hash,
        "previous_residual_count": 57 if stage == "sharp" else 53,
        "remaining_residual_count": remaining,
        "parents": parents, "link_audits": audits, "axioms": profiles,
        "root": root.name, "root_sha256": a68.sha(root), "delta_objects": hashes,
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "exact_at_champion_score": ns + ".exact_at_champion_score",
    }
    (delta / "delta.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    shutil.rmtree(inputs)
    print(f"PASS: {remaining} residuals; {len(hashes)} new objects", flush=True)


if __name__ == "__main__":
    main()
