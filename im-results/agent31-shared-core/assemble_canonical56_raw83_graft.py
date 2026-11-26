#!/usr/bin/env python3
"""Consume Raw83 after the accepted Raw113 -> Raw112 -> Raw59 Canonical56 chain."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
REPO = "FlareZ123/bb6"
NS = "BB6.Agent31Canonical55Raw83Graft"
NS56 = "BB6.Agent31Canonical56Raw83Membership"
BASE_ARTIFACT = "canonical56-raw59-graft-integrated"
BASE_MODULE = "Canonical56Raw59Graft"

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


def verify_base(a68, work: Path, run_id: int):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", run.get("conclusion")
    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["name"] == BASE_ARTIFACT]
    assert len(matches) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = matches[0]
    assert not item["expired"] and item["digest"].startswith("sha256:")
    digest = item["digest"].removeprefix("sha256:")
    pin = (item["id"], run_id, digest)
    dirs = a68.download(pin, work)

    choices = []
    for root in dirs:
        for candidate in (root, root / "linked"):
            if (candidate / f"{BASE_MODULE}.olean").is_file():
                choices.append(candidate)
    assert len(choices) == 1, [str(p) for p in choices]
    linked = choices[0]

    metadata = work / "metadata" / str(item["id"])
    reports = list(metadata.rglob("canonical56-raw59-graft.json"))
    assert len(reports) == 1, [str(p) for p in reports]
    report = json.loads(reports[0].read_text())
    assert report["source_revision"] == run["head_sha"]
    assert report["canonical57_residual_count"] == 57
    assert report["remaining_residual_count"] == 56
    assert report["raw113_consumed"] and report["raw112_consumed"]
    assert report["raw59_consumed"]
    assert report["raw113_removed"] and report["raw112_removed"]
    assert report["olean_sha256"] == a68.sha(linked / f"{BASE_MODULE}.olean")
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return linked, pin, item, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--canonical56-run-id", required=True, type=int)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    import assemble_canonical68 as a68
    import assemble_canonical59_five_parent as five
    import assemble_canonical_selected as selected

    base_work = work / "base"
    raw83_work = work / "raw83"
    base_work.mkdir()
    raw83_work.mkdir()

    linked, base_pin, base_artifact, base_report = verify_base(
        a68, base_work, args.canonical56_run_id
    )
    raw83_dirs, raw83_metadata = five.download_parent(RAW83_SPEC, raw83_work)
    copied = []
    raw83_link_audit = {}
    selected.add_family(RAW83_SPEC, raw83_dirs, linked, copied, raw83_link_audit)
    env = dict(os.environ, LEAN_PATH=str(linked))

    membership58_source = HERE / "Canonical58Raw83Membership.lean"
    membership58_output = linked / f"{membership58_source.stem}.olean"
    assert not membership58_output.exists()
    membership58_log = a68.compile_module(
        membership58_source, membership58_output, env,
        work / "canonical58-raw83-membership.log"
    )
    membership58_profiles = a68.gate(membership58_log, [
        "BB6.Agent31Canonical58Raw83Membership.p83_root",
        "BB6.Agent31Canonical58Raw83Membership.p83_count58",
        "BB6.Agent31Canonical58Raw83Membership.p83_distinct_from_p113",
    ])

    membership_source = HERE / "Canonical56Raw83Membership.lean"
    membership_output = linked / f"{membership_source.stem}.olean"
    assert not membership_output.exists()
    membership_log = a68.compile_module(
        membership_source, membership_output, env,
        work / "canonical56-raw83-membership.log"
    )
    membership_profiles = a68.gate(membership_log, [
        NS56 + ".p83_count56",
        NS56 + ".p83_distinct_from_previous",
        NS56 + ".p83_source_eq",
        NS56 + ".p83_root",
        NS56 + ".p83_cover",
    ])

    source = HERE / "Canonical55Raw83Graft.lean"
    output = linked / f"{source.stem}.olean"
    assert not output.exists()
    log = a68.compile_module(
        source, output, env, work / "canonical55-raw83-graft.log"
    )
    profiles = a68.gate(log, [
        NS + "." + name for name in (
            "p83_count56", "p83_removed", "count55", "raw59_removed",
            "raw112_removed", "raw113_removed", "parents_pairwise_distinct",
            "parents_root", "parents_cover", "sound_integrated",
            "exact_at_target", "exact_at_champion_score",
        )
    ])

    generated = work / "generated"
    generated.mkdir()
    for src in (membership58_source, membership_source, source):
        shutil.copy2(src, generated / src.name)
    (generated / "canonical56-base-report.json").write_text(
        json.dumps(base_report, indent=2) + "\n"
    )
    (generated / "raw83-parent-spec.json").write_text(
        json.dumps(RAW83_SPEC, indent=2) + "\n"
    )

    report = {
        "status": "kernel-checked Canonical56-to-55 Raw83 delta",
        "canonical56_run_id": args.canonical56_run_id,
        "canonical56_artifact_name": base_artifact["name"],
        "canonical56_artifact_id": base_pin[0],
        "canonical56_artifact_sha256": base_pin[2],
        "canonical56_source_revision": base_report["source_revision"],
        "canonical56_olean_sha256": base_report["olean_sha256"],
        "canonical56_residual_count": 56,
        "raw113_consumed": True,
        "raw112_consumed": True,
        "raw59_consumed": True,
        "raw83_run_id": RAW83_SPEC["run_id"],
        "raw83_artifact_id": raw83_metadata["artifact_id"],
        "raw83_artifact_name": raw83_metadata["artifact_name"],
        "raw83_artifact_sha256": raw83_metadata["artifact_digest"],
        "raw83_parent_table": RAW83_SPEC["table"],
        "raw83_parent_theorem": RAW83_SPEC["theorem"],
        "raw83_weighted_bound": RAW83_SPEC["bound"],
        "raw83_link_audit": raw83_link_audit,
        "raw83_copied_modules": copied,
        "canonical58_membership_axioms": membership58_profiles,
        "canonical56_membership_axioms": membership_profiles,
        "axioms": profiles,
        "remaining_residual_count": 55,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    (work / "canonical55-raw83-graft.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
