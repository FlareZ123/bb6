#!/usr/bin/env python3
"""Consume source-accepted Raw106 and Raw79 Covers from accepted Canonical57."""

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

BASE_RUN = 45910336799
BASE_ARTIFACT = "canonical58-raw113-graft-integrated"
BASE_ARTIFACT_ID = 15159933665
BASE_ARTIFACT_SHA = "7c912dc7cff20dd796dad9e0008c6fbc9558f81bc9dcc13eb399b4393a73e140"
BASE_ARTIFACT_SIZE = 22949946864
BASE_SOURCE_REVISION = "8f91f38a2ac75dbb2adef4ca82feb4ec694ef26e"

PARENT_RUN = 45878084731
PARENT_SOURCE_REVISION = "75e7dcf16f98efda9ab3323b0acc16633833f180"

PARENTS = {
    "106": {
        "label": "raw106",
        "artifact_id": 15147725126,
        "artifact_name": "agent10-raw106-canonical64-parent-source-accepted",
        "digest": "1f4fbd81b26b300319e229eea0893e2d0998cb480704a237f61afef84db87b85",
        "size": 26661334,
        "root": "Raw106ParentCover",
        "theorem": "BB6.Agent10Raw106.parent_cover",
        "table": "1RB---_1RC1RF_0RD---_1LD1RE_---0LB_------",
        "bound": 253,
    },
    "79": {
        "label": "raw79",
        "artifact_id": 15148575654,
        "artifact_name": "agent10-raw79-canonical64-parent-source-accepted",
        "digest": "b0f95044a83bee3bd90f640a275c9ae8a2fadd754cc25d333cb434532be2b99c",
        "size": 23624160,
        "root": "Raw79ParentCover",
        "theorem": "BB6.Agent10Raw79.parent_cover",
        "table": "1RB---_1RC1LE_0RD---_1LD1RE_---0LB_------",
        "bound": 2354,
    },
}

NS = "BB6.Agent31Canonical55Raw106Raw79Graft"


def verify_base(work: Path):
    run = a68.api_json(f"repos/{REPO}/actions/runs/{BASE_RUN}")
    assert run["conclusion"] == "success", run.get("conclusion")
    assert run["head_sha"] == BASE_SOURCE_REVISION, (run["head_sha"], BASE_SOURCE_REVISION)

    artifacts = a68.api_json(
        f"repos/{REPO}/actions/runs/{BASE_RUN}/artifacts?per_page=100"
    )["artifacts"]
    matches = [x for x in artifacts if x["name"] == BASE_ARTIFACT]
    assert len(matches) == 1, [(x["id"], x["name"]) for x in artifacts]
    item = matches[0]
    assert item["id"] == BASE_ARTIFACT_ID, item["id"]
    assert item["size_in_bytes"] == BASE_ARTIFACT_SIZE, item["size_in_bytes"]
    assert item["digest"] == "sha256:" + BASE_ARTIFACT_SHA, item["digest"]
    assert not item["expired"], item["id"]

    dirs = a68.download((item["id"], BASE_RUN, BASE_ARTIFACT_SHA), work)
    roots = [
        p for p in work.rglob("Raw124Canonical58Membership.olean")
        if "metadata" not in p.parts
    ]
    assert len(roots) == 1, [str(p) for p in roots]
    linked = roots[0].parent
    assert (linked / "Canonical58Raw113Graft.olean").is_file()
    assert (linked / "Raw124ParentComplete.olean").is_file()

    reports = [
        p for p in work.rglob("raw124-canonical58-membership.json")
        if "metadata" not in p.parts
    ]
    assert len(reports) == 1, [str(p) for p in reports]
    report_path = reports[0]
    report = json.loads(report_path.read_text())
    assert report["status"] == "source-accepted Canonical58-to-57 Raw124 delta"
    assert report["canonical58_source_revision"] == run["head_sha"]
    assert report["canonical58_residual_count"] == 58
    assert report["canonical57_residual_count"] == 57
    assert report["raw124_unique_membership_in_canonical58"]
    assert report["graft_olean_sha256"] == a68.sha(
        linked / "Raw124Canonical58Membership.olean"
    )
    assert "sorryAx" not in str(report["axioms"])
    assert "native_decide" not in str(report["axioms"])
    return linked, item, report_path, report


def verify_parent(raw: str, work: Path):
    spec = PARENTS[raw]
    run = a68.api_json(f"repos/{REPO}/actions/runs/{PARENT_RUN}")
    # The overall matrix run failed only because Raw67 failed. Raw106/79 each
    # uploaded their source-accepted artifact after their own compile gate.
    assert run["head_sha"] == PARENT_SOURCE_REVISION, (
        run["head_sha"], PARENT_SOURCE_REVISION
    )

    info = a68.api_json(f"repos/{REPO}/actions/artifacts/{spec['artifact_id']}")
    assert info["workflow_run"]["id"] == PARENT_RUN, info["workflow_run"]
    assert info["name"] == spec["artifact_name"], info["name"]
    assert info["size_in_bytes"] == spec["size"], info["size_in_bytes"]
    assert info["digest"] == "sha256:" + spec["digest"], info["digest"]
    assert not info["expired"], spec["artifact_id"]

    dirs = a68.download(
        (spec["artifact_id"], PARENT_RUN, spec["digest"]), work
    )
    assert any((d / (spec["root"] + ".olean")).is_file() for d in dirs), (
        raw, spec["root"], [str(d) for d in dirs]
    )

    reports = list((work / "metadata" / str(spec["artifact_id"])).rglob("report.json"))
    candidates = []
    for path in reports:
        try:
            report = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if str(report.get("raw")) == raw:
            candidates.append((path, report))
    assert len(candidates) == 1, [str(p) for p, _ in candidates]
    report_path, report = candidates[0]

    assert report["source_revision"] == PARENT_SOURCE_REVISION
    assert "4.36.0-rc2" in report["lean_version"]
    assert "source-accepted" in report["status"]
    parent = report["parent"]
    assert parent["cover_theorem"] == spec["theorem"], parent
    assert parent["table"] == spec["table"], parent
    assert parent["bound"] == spec["bound"], parent
    assert "sorryAx" not in str(parent["axioms"])
    assert "native_decide" not in str(parent["axioms"])
    return dirs, report_path, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    args = parser.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in lean_version, lean_version

    base_work = work / "base"
    parent106_work = work / "raw106"
    parent79_work = work / "raw79"
    base_work.mkdir()
    parent106_work.mkdir()
    parent79_work.mkdir()

    linked, base_item, base_report_path, base_report = verify_base(base_work)

    copied = []
    audits = {}
    parent_reports = {}
    for raw, parent_work in (("106", parent106_work), ("79", parent79_work)):
        dirs, report_path, report = verify_parent(raw, parent_work)
        audit = {}
        selected.add_family(PARENTS[raw], dirs, linked, copied, audit)
        audits[raw] = audit
        parent_reports[raw] = (report_path, report)

    source = HERE / "Canonical55Raw106Raw79Graft.lean"
    output = linked / f"{source.stem}.olean"
    assert not output.exists(), output
    env = dict(os.environ, LEAN_PATH=str(linked))
    log_path = work / "canonical55-raw106-raw79-graft.log"
    log = a68.compile_module(source, output, env, log_path)

    required = [
        NS + "." + name for name in (
            "p106_count57", "p79_count57", "p106_p79_distinct",
            "p106_root", "p79_root", "p106_cover", "p79_cover",
            "count55", "p106_removed", "p79_removed", "sound_integrated",
            "exact_at_target", "exact_at_champion_score",
        )
    ]
    profiles = a68.gate(log, required)

    generated = work / "generated"
    generated.mkdir()
    shutil.copy2(source, generated / source.name)
    shutil.copy2(base_report_path, generated / "canonical57-base-report.json")
    for raw, (report_path, report) in parent_reports.items():
        shutil.copy2(report_path, generated / f"raw{raw}-parent-report.json")

    report = {
        "status": "source-accepted Canonical57-to-55 Raw106+Raw79 delta",
        "lean_version": lean_version,
        "canonical57_run_id": BASE_RUN,
        "canonical57_artifact_id": BASE_ARTIFACT_ID,
        "canonical57_artifact_name": base_item["name"],
        "canonical57_artifact_sha256": BASE_ARTIFACT_SHA,
        "canonical57_source_revision": BASE_SOURCE_REVISION,
        "canonical57_residual_count": 57,
        "canonical57_olean_sha256": a68.sha(
            linked / "Raw124Canonical58Membership.olean"
        ),
        "parents": {
            raw: {
                **PARENTS[raw],
                "run_id": PARENT_RUN,
                "source_revision": PARENT_SOURCE_REVISION,
                "artifact_id": PARENTS[raw]["artifact_id"],
                "artifact_name": PARENTS[raw]["artifact_name"],
                "artifact_sha256": PARENTS[raw]["digest"],
                "link_audit": audits[raw],
            }
            for raw in ("106", "79")
        },
        "raw106_unique_membership_in_canonical57": True,
        "raw79_unique_membership_in_canonical57": True,
        "raw106_raw79_distinct": True,
        "raw106_removed": True,
        "raw79_removed": True,
        "raw124_already_removed": True,
        "remaining_residual_count": 55,
        "axioms": profiles,
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
    }
    report_path = work / "canonical55-raw106-raw79-graft.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
