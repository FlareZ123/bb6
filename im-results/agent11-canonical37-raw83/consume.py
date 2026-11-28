#!/usr/bin/env python3
"""Consume source-accepted Raw83 after an authenticated direct Canonical38."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "agent50-raw47-canonical41"))
sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))

import consume_after_canonical40 as ca
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected

c = ca.c
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RAW83 = {
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
TARGETS = [
    "BB6.Agent11Canonical37Raw83.p83_root",
    "BB6.Agent11Canonical37Raw83.p83_count38",
    "BB6.Agent11Canonical37Raw83.count37",
    "BB6.Agent11Canonical37Raw83.p83_removed",
    "BB6.Agent11Canonical37Raw83.p83_source_eq",
    "BB6.Agent11Canonical37Raw83.p83_cover_at_champion",
    "BB6.Agent11Canonical37Raw83.sound37_at_champion",
    "BB6.Agent11Canonical37Raw83.exact_at_champion_score",
]


def sh(*args):
    return subprocess.check_output(args, text=True).strip()


def restore_direct38(work: Path, run_id: int):
    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = ca.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40

    meta = json.loads(sh(
        "gh", "api",
        f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{run_id}",
    ))
    assert meta["conclusion"] == "success"
    assert meta["event"] == "workflow_dispatch"
    assert meta["path"] == ".github/workflows/agent3-canonical38-direct.yml"

    downloaded = work / "direct38"
    subprocess.run([
        "gh", "run", "download", str(run_id),
        "-n", "canonical38-raw39-raw47-direct-delta",
        "-D", str(downloaded),
    ], check=True)

    receipts = list(downloaded.rglob("delta.json"))
    assert len(receipts) == 1, receipts
    receipt = json.loads(receipts[0].read_text())
    delta = receipts[0].parent
    assert receipt["source_revision"] == meta["head_sha"]
    assert receipt["previous_residual_count"] == 40
    assert receipt["remaining_residual_count"] == 38
    assert receipt["exact_at_champion_score"] == (
        "BB6.Agent3Canonical38Raw39Raw47Direct.exact_at_champion_score"
    )
    assert receipt["raw47_run_id"] == 46068688341
    assert receipt["onele_run"] == 46114235329

    objects = delta / "objects"
    for name, digest in receipt["delta_objects"].items():
        src = objects / name
        assert src.is_file(), src
        assert c.a68.sha(src) == digest, name
        dst = linked / name
        if dst.exists():
            assert c.a68.sha(dst) == digest, name
        else:
            shutil.copy2(src, dst)
    assert (linked / "Canonical38Raw39Raw47Direct.olean").is_file()
    return linked, receipt, meta, pin40


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--canonical38-run", type=int, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical37-raw83-after-direct38-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

    linked, receipt38, meta38, pin40 = restore_direct38(
        work / "base", args.canonical38_run
    )

    raw83_work = work / "raw83-parent"
    raw83_work.mkdir()
    raw83_dirs, raw83_meta = five.download_parent(RAW83, raw83_work)
    copied = []
    raw83_audit = {}
    selected.add_family(RAW83, raw83_dirs, linked, copied, raw83_audit)
    assert (linked / "A10Raw83Exact.olean").is_file()

    root, profiles = c.u.compile_one(
        HERE / "Canonical37Raw83.lean", linked, evidence, TARGETS
    )
    if not set(TARGETS) <= set(profiles):
        raise RuntimeError(
            "missing axiom profiles: " + repr(set(TARGETS) - set(profiles))
        )
    if not all(set(ax) <= ALLOWED for ax in profiles.values()):
        raise RuntimeError("unapproved axiom profile: " + repr(profiles))

    new_objects = [*copied, root]
    hashes = {}
    for src in new_objects:
        dest = objects / src.name
        digest = c.a68.sha(src)
        if dest.exists():
            assert c.a68.sha(dest) == digest, src.name
        else:
            shutil.copy2(src, dest)
        hashes[dest.name] = digest

    out = {
        "status": (
            "source-accepted Raw83 successor of authenticated direct Canonical38"
        ),
        "source_revision": sh("git", "rev-parse", "HEAD"),
        "canonical38_run": args.canonical38_run,
        "canonical38_head_sha": meta38["head_sha"],
        "canonical38_receipt": receipt38,
        "previous_delta": pin40,
        "previous_residual_count": 38,
        "remaining_residual_count": 37,
        "raw83_parent": raw83_meta,
        "raw83_link_audit": raw83_audit,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": hashes[root.name],
        "delta_objects": hashes,
        "exact_at_champion_score": (
            "BB6.Agent11Canonical37Raw83.exact_at_champion_score"
        ),
    }
    (delta / "delta.json").write_text(
        json.dumps(out, indent=2, sort_keys=True) + "\n"
    )
    print(
        "PASS: accepted Raw83 consumed from authenticated direct Canonical38; "
        "exactly 37 quotient Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
