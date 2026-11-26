#!/usr/bin/env python3
"""Add the source-accepted Raw113 parent to a verified 59-residual Canonical64 consumer.

The base run is discovered by artifact name and its own JSON report is checked.
Only the Raw113 import closure is added; the already accepted parent proofs are
not rebuilt. The final Lean theorem is a delta from the base quotient soundness.
"""
import argparse
import json
import os
from pathlib import Path

import assemble_canonical68 as a68
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected

HERE = Path(__file__).resolve().parent
REPO = "FlareZ123/bb6"
NS = "BB6.Agent31Canonical58Raw113Graft"
RAW113_SPEC = selected.RAW113_SPEC


def verify_base(work, run_id):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    candidates = [x for x in artifacts
                  if x["name"] == "canonical64-selected-parent-integrated"]
    assert len(candidates) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = candidates[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")
    pin = (item["id"], run_id, digest)
    dirs = a68.download(pin, work)
    choices = [p for p in dirs if (p / "CanonicalSelectedParentIntegrated.olean").is_file()]
    assert len(choices) == 1
    linked = choices[0]
    reports = list((work / "metadata" / str(item["id"])).rglob("selected-integration.json"))
    assert len(reports) == 1
    report = json.loads(reports[0].read_text())
    accepted = {x["label"] for x in report["accepted"]}
    assert report["source_revision"] == run["head_sha"]
    assert report["base_residual_count"] == 64
    assert report["remaining_residual_count"] == 59
    assert {"raw119", "raw115", "raw58", "raw108", "raw118"} <= accepted
    assert report["raw59_retained"] and not report["rejected"]
    assert report["olean_sha256"] == a68.sha(linked / "CanonicalSelectedParentIntegrated.olean")
    return linked, pin, item, report


def add_raw113(work, linked):
    dirs, metadata = five.download_parent(RAW113_SPEC, work)
    copied = []
    audit = {}
    selected.add_family(RAW113_SPEC, dirs, linked, copied, audit)
    return copied, metadata, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--base-run-id", required=True, type=int)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    linked, base_pin, base_artifact, base_report = verify_base(work, args.base_run_id)
    copied, parent_metadata, link_audit = add_raw113(work, linked)
    env = dict(os.environ, LEAN_PATH=str(linked))

    membership_source = HERE / "Canonical59Raw113Membership.lean"
    membership_output = linked / (membership_source.stem + ".olean")
    assert not membership_output.exists()
    membership_log = a68.compile_module(
        membership_source, membership_output, env, work / "raw113-membership.log"
    )
    membership_profiles = a68.gate(membership_log, [
        "BB6.Agent31Canonical59Raw113Membership.p113_source_eq",
        "BB6.Agent31Canonical59Raw113Membership.p113_count64",
        "BB6.Agent31Canonical59Raw113Membership.p113_count59",
        "BB6.Agent31Canonical59Raw113Membership.p113_root",
        "BB6.Agent31Canonical59Raw113Membership.p113_cover",
    ])

    source = HERE / "Canonical58Raw113Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists()
    log = a68.compile_module(source, output, env, work / "canonical58-raw113-graft.log")
    profiles = a68.gate(log, [NS + "." + n for n in (
        "p113_count59", "count58", "raw59_retained", "parents_pairwise_distinct",
        "parents_root", "parents_cover", "sound_integrated", "exact_at_target",
        "exact_at_champion_score")])

    generated = work / "generated"
    generated.mkdir()
    import shutil
    shutil.copy2(membership_source, generated / membership_source.name)
    shutil.copy2(source, generated / source.name)
    (generated / "base-selected-integration.json").write_text(
        json.dumps(base_report, indent=2) + "\\n"
    )
    (generated / "raw113-parent-spec.json").write_text(
        json.dumps(RAW113_SPEC, indent=2) + "\\n"
    )

    report = {
        "status": "kernel-checked Canonical59-to-58 Raw113 delta",
        "base_run_id": args.base_run_id,
        "base_pin": base_pin,
        "base_artifact_name": base_artifact["name"],
        "base_artifact_sha256": base_artifact["digest"].removeprefix("sha256:"),
        "base_source_revision": base_report["source_revision"],
        "base_olean_sha256": base_report["olean_sha256"],
        "base_residual_count": 59,
        "remaining_residual_count": 58,
        "base_accepted": [x["label"] for x in base_report["accepted"]],
        "raw59_retained": True,
        "raw113_parent": parent_metadata,
        "raw113_link_audit": link_audit,
        "membership_axioms": membership_profiles,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": __import__("subprocess").check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical58-raw113-graft.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
