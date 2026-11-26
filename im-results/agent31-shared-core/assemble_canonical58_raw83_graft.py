#!/usr/bin/env python3
"""Add the source-accepted Raw83 parent to the current 58-residual Canonical58 base.

The base is the Canonical59-to-58 Raw113 delta. Only the Raw83 source closure
is added; the previous parent Covers are not rebuilt.
"""
import argparse
import json
import os
import shutil
import subprocess
from pathlib import Path

import assemble_canonical68 as a68
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected

HERE = Path(__file__).resolve().parent
REPO = "FlareZ123/bb6"
NS = "BB6.Agent31Canonical57Raw83Graft"
RAW83_SPEC = {
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


def verify_base(work, run_id):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    candidates = [x for x in artifacts
                  if x["name"] == "canonical58-raw113-graft-integrated"]
    assert len(candidates) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = candidates[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    pin = (item["id"], run_id, item["digest"].removeprefix("sha256:"))
    dirs = a68.download(pin, work)
    choices = [p for p in dirs if (p / "Canonical58Raw113Graft.olean").is_file()]
    assert len(choices) == 1
    linked = choices[0]
    reports = list((work / "metadata" / str(item["id"])).rglob("canonical58-raw113-graft.json"))
    assert len(reports) == 1
    report = json.loads(reports[0].read_text())
    assert report["source_revision"] == run["head_sha"]
    assert report["base_residual_count"] == 59
    assert report["remaining_residual_count"] == 58
    assert report["raw59_retained"] is True
    assert "raw118" in report["base_accepted"]
    assert report["olean_sha256"] == a68.sha(linked / "Canonical58Raw113Graft.olean")
    return linked, pin, item, report


def add_raw83(work, linked):
    dirs, metadata = five.download_parent(RAW83_SPEC, work)
    copied = []
    audit = {}
    selected.add_family(RAW83_SPEC, dirs, linked, copied, audit)
    return metadata, copied, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--base-run-id", required=True, type=int)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    linked, base_pin, base_artifact, base_report = verify_base(work, args.base_run_id)
    parent_metadata, copied, link_audit = add_raw83(work, linked)
    env = dict(os.environ, LEAN_PATH=str(linked))

    membership_source = HERE / "Canonical58Raw83Membership.lean"
    membership_output = linked / (membership_source.stem + ".olean")
    assert not membership_output.exists()
    membership_log = a68.compile_module(
        membership_source, membership_output, env, work / "raw83-membership.log"
    )
    membership_profiles = a68.gate(membership_log, [
        "BB6.Agent31Canonical58Raw83Membership.p83_root",
        "BB6.Agent31Canonical58Raw83Membership.p83_count58",
        "BB6.Agent31Canonical58Raw83Membership.p83_distinct_from_p113",
    ])

    source = HERE / "Canonical57Raw83Graft.lean"
    output = linked / (source.stem + ".olean")
    assert not output.exists()
    log = a68.compile_module(source, output, env, work / "canonical57-raw83-graft.log")
    profiles = a68.gate(log, [NS + "." + n for n in (
        "p83_source_eq", "p83_cover", "count57", "raw59_retained",
        "parents_pairwise_distinct", "parents_root", "parents_cover",
        "sound_integrated", "exact_at_target", "exact_at_champion_score")])

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(membership_source, generated / membership_source.name)
    shutil.copy2(source, generated / source.name)
    (generated / "base-canonical58-raw113-report.json").write_text(
        json.dumps(base_report, indent=2) + "\n"
    )
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(RAW83_SPEC, indent=2) + "\n"
    )

    report = {
        "status": "kernel-checked Canonical58-to-57 Raw83 delta",
        "base_run_id": args.base_run_id,
        "base_pin": base_pin,
        "base_artifact_name": base_artifact["name"],
        "base_artifact_sha256": base_artifact["digest"].removeprefix("sha256:"),
        "base_source_revision": base_report["source_revision"],
        "base_olean_sha256": base_report["olean_sha256"],
        "base_residual_count": 58,
        "remaining_residual_count": 57,
        "base_raw59_retained": True,
        "raw83_parent": parent_metadata,
        "raw83_link_audit": link_audit,
        "membership_axioms": membership_profiles,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical57-raw83-graft.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
