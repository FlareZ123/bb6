#!/usr/bin/env python3
"""Consume accepted Raw47, Raw83, Raw112 together after accepted Raw39."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
REPO = HERE.parents[1]
A9 = SIBLINGS / "agent9-canonical38-official"
A11 = SIBLINGS / "agent11-raw39"
A31 = SIBLINGS / "agent31-shared-core"
A17 = SIBLINGS / "agent17-raw112-canonical58"
sys.path.insert(0, str(A9))
sys.path.insert(0, str(A31))
sys.path.insert(0, str(A17))

import consume as official
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected
from assemble_canonical58_raw112_graft import verify_raw112_parent

c = official.c
raw47 = official.raw47
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
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
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
NS = "BB6.Agent10Raw47Raw83Raw112Canonical36AfterRaw39"
TARGETS = [
    NS + ".p47_count39",
    NS + ".p83_count39",
    NS + ".p112_count39",
    NS + ".parents_pairwise",
    NS + ".p47_cover",
    NS + ".p83_cover",
    NS + ".p112_cover",
    NS + ".count36",
    NS + ".raw47_removed",
    NS + ".raw83_removed",
    NS + ".raw112_removed",
    NS + ".sound_integrated",
    NS + ".sound_at",
    NS + ".exact_at_champion_score",
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--direct38-run-id", type=int, required=True)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    accepted39 = official.authenticate_accepted39(evidence)

    # Reconstruct exact Canonical40 and authenticate the accepted direct
    # Raw39+Raw47 transport carrier.  This gives Raw47KernelBridge in the same
    # source environment without replaying the 2.26 GB Raw47 parent closure.
    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = raw47.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40

    transport_report, transport_pin, _ = official.restore_transport(
        work, linked, prior40, pin40, args.direct38_run_id)

    profiles = {}
    roots = {}
    root39, ax39 = official.source_check(
        A11 / "Raw39Canonical39Successor.lean",
        linked, evidence, official.RAW39_TARGETS)
    roots[root39.name] = c.a68.sha(root39)
    profiles.update(ax39)

    # Add compact accepted Raw83 proof family.
    raw83_work = work / "raw83-parent"
    raw83_work.mkdir()
    raw83_dirs, raw83_meta = five.download_parent(RAW83_SPEC, raw83_work)
    raw83_copied = []
    raw83_audit = {}
    selected.add_family(
        RAW83_SPEC, raw83_dirs, linked, raw83_copied, raw83_audit)
    assert (linked / "A10Raw83Exact.olean").is_file()

    # Add complete source-accepted Raw112 proof family.
    raw112_work = work / "raw112-parent"
    raw112_work.mkdir()
    raw112_meta, raw112_dirs, raw112_summary = verify_raw112_parent(
        raw112_work, args.raw112_run_id)
    raw112_copied = []
    raw112_audit = {}
    selected.add_family(
        {"root": "Raw112ClosedCover"},
        raw112_dirs, linked, raw112_copied, raw112_audit)
    assert (linked / "Raw112ClosedCover.olean").is_file()

    source = HERE / "Raw47Raw83Raw112Canonical36AfterRaw39.lean"
    root, final_profiles = official.source_check(
        source, linked, evidence, TARGETS)
    roots[root.name] = c.a68.sha(root)
    profiles.update(final_profiles)
    assert all(set(v) <= ALLOWED for v in profiles.values()), profiles

    report = {
        "status": (
            "source-checked Raw47 plus Raw83 plus Raw112 successor of "
            "accepted Raw39 Canonical39"),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "accepted_canonical39": accepted39,
        "canonical40_delta": pin40,
        "canonical40_root_sha256": prior40["root_sha256"],
        "raw47_transport_carrier": transport_pin,
        "raw47_transport_status": transport_report["status"],
        "previous_residual_count": 39,
        "remaining_residual_count": 36,
        "raw83_parent": RAW83_SPEC,
        "raw83_artifact": raw83_meta,
        "raw83_link_audit": raw83_audit,
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": raw112_meta["artifact_name"],
        "raw112_artifact_id": raw112_meta["artifact_id"],
        "raw112_artifact_sha256": raw112_meta["artifact_digest"],
        "raw112_parent_table": RAW112_TABLE,
        "raw112_parent_theorem": "BB6.Agent47Raw112.parent_cover",
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": raw112_summary,
        "raw112_link_audit": raw112_audit,
        "theorems": profiles,
        "roots": roots,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
    }
    (evidence / "raw47-raw83-raw112-after-raw39-canonical36.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw39 Canonical39 -> Raw47 + Raw83 + Raw112 -> "
        "Canonical36; exactly 36 Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
