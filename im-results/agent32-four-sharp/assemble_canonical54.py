#!/usr/bin/env python3
"""Consume four independently accepted sharp parents directly at Canonical58.

Export only the newly linked project objects and two consumer modules. The
base artifact remains pinned; no multi-gigabyte duplicate base upload.
"""
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
sys.path.insert(0, str(ROOT / "im-results" / "agent31-raw106-79-canonical55"))
import assemble_canonical68 as a68
import assemble_canonical_selected as selected
import assemble_canonical53_from58 as base
from assemble_canonical47_sharp_after_eight import SPECS as OLD_SPECS

REPO = "FlareZ123/bb6"
NS = "BB6.Agent32Canonical54FourSharp"
SHARP_RUN = 45919568346
SHARP_REVISION = "fc71d53353958fd92100191242692dbcbfe00360"
SPECS = {
    **{k: dict(v, run_id=SHARP_RUN, revision=SHARP_REVISION)
       for k, v in OLD_SPECS.items()},
    "99": dict(label="raw99", run_id=45926296755,
               revision="2495b790e8650dd55a007ce950329f8530a55c9f",
               artifact_id=15166288975, artifact_name="raw99-sharp-certified",
               digest="c8c88c253f130b162f9c7b3f99ebe7dedafb0af24ab14261b56c0c9d95e8673b",
               size=12696669, root="Raw99Data",
               theorem="BB6.Agent2Raw99.exact99", bound=196),
}
assert set(SPECS) == {"95", "99", "103", "105"}

def verify_parent(spec, work):
    aid = spec["artifact_id"]
    run = a68.api_json(f"repos/{REPO}/actions/runs/{spec['run_id']}")
    assert run["head_sha"] == spec["revision"]
    # The three older artifacts came from successful jobs of a partially
    # failed matrix. Require the accepted artifact and its actual module gate,
    # not the aggregate matrix conclusion.
    if spec["run_id"] != SHARP_RUN:
        assert run["conclusion"] == "success"
    item = a68.api_json(f"repos/{REPO}/actions/artifacts/{aid}")
    assert item["name"] == spec["artifact_name"]
    assert item["size_in_bytes"] == spec["size"]
    assert item["workflow_run"]["head_sha"] == spec["revision"]
    dirs = a68.download((aid, spec["run_id"], spec["digest"]), work)
    # a68.download places JSON in metadata/<artifact id>, separate from objects.
    candidates = []
    for path in (work / "metadata" / str(aid)).rglob("*.json"):
        manifest = json.loads(path.read_text())
        claim = manifest.get("claim") or {}
        if claim.get("theorem") == spec["theorem"]:
            candidates.append((path, manifest))
    assert len(candidates) == 1, (aid, [str(p) for p, _ in candidates])
    path, manifest = candidates[0]
    assert manifest["proof_source_revision"] == spec["revision"]
    assert "4.36.0-rc2" in manifest["lean_version"]
    assert manifest["claim"]["weighted_bound"] == spec["bound"]
    assert any(x["module"] == spec["root"] for x in manifest["roots"])
    root = [d / (spec["root"] + ".olean") for d in dirs
            if (d / (spec["root"] + ".olean")).is_file()]
    assert len(root) == 1
    module = next(x for x in manifest["modules"] if x["module"] == spec["root"])
    assert module["olean_sha256"] == a68.sha(root[0])
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert manifest["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")
    return dirs, path

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "delta"
    objects = delta / "objects"
    evidence = delta / "evidence"
    objects.mkdir(parents=True)
    evidence.mkdir()
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version
    # Validate small inputs before fetching the expensive base.
    families = []
    for raw, spec in SPECS.items():
        folder = work / ("raw" + raw)
        folder.mkdir()
        dirs, manifest = verify_parent(spec, folder)
        shutil.copy2(manifest, evidence / f"raw{raw}-manifest.json")
        families.append((spec, dirs))
    base_work = work / "base"
    base_work.mkdir()
    linked, base_item, base_report_path, base_report = base.verify_base(base_work)
    shutil.copy2(base_report_path, evidence / "canonical58-base-report.json")
    copied = []
    audits = {}
    for spec, dirs in families:
        audit = {}
        selected.add_family(spec, dirs, linked, copied, audit)
        audits[spec["label"]] = audit
    env = dict(os.environ, LEAN_PATH=str(linked))
    profiles = {}
    for stem, required in [
        ("FourSharpCover", ["BB6.Agent32FourSharp.parent_covers",
                            "BB6.Agent32FourSharp.union_exact"]),
        ("Canonical54FourSharpGraft", [
            NS + "." + n for n in ("unique_membership", "pairwise_distinct",
            "parents_root", "parents_cover", "count54", "all_removed",
            "raw59_retained", "sound_integrated", "exact_at_target",
            "exact_at_champion_score")]),
    ]:
        source = HERE / (stem + ".lean")
        output = linked / (stem + ".olean")
        assert not output.exists(), output
        log = a68.compile_module(source, output, env, evidence / (stem + ".log"))
        profiles.update(a68.gate(log, required))
        copied.append(output)
        shutil.copy2(source, evidence / source.name)
    hashes = {}
    for path in copied:
        target = objects / path.name
        assert not target.exists(), target
        shutil.copy2(path, target)
        hashes[path.name] = a68.sha(target)
    report = dict(status="source-accepted direct Canonical58-to-54 four-sharp delta",
        lean_version=version, base_run_id=base.BASE_RUN,
        base_artifact_id=base_item["id"], base_artifact_sha256=base.BASE_ARTIFACT_SHA,
        base_source_revision=base.BASE_SOURCE_REVISION,
        base_olean_sha256=base_report["olean_sha256"], base_residual_count=58,
        remaining_residual_count=54, all_four_unique_membership=True,
        all_four_pairwise_distinct=True, raw59_retained=True,
        parents=SPECS, link_audits=audits, axioms=profiles, delta_objects=hashes,
        root="Canonical54FourSharpGraft",
        olean_sha256=hashes["Canonical54FourSharpGraft.olean"],
        exact_at_champion_score=NS + ".exact_at_champion_score",
        source_revision=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip())
    (delta / "canonical54-four-sharp-delta.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"PASS: four unique source-checked cuts; {len(hashes)} new objects", flush=True)

if __name__ == "__main__":
    main()
