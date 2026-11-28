#!/usr/bin/env python3
"""Authenticate Agent3 direct Canonical38 and source-check Raw43 conditional 38->37."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent50-raw47-canonical41"))
import consume_after_canonical40 as ca

c = ca.c
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = [
    "BB6.Agent25Raw43Canonical38DirectConditional.parent_count38",
    "BB6.Agent25Raw43Canonical38DirectConditional.count37",
    "BB6.Agent25Raw43Canonical38DirectConditional.removed_parent_absent",
    "BB6.Agent25Raw43Canonical38DirectConditional.conditional_sound",
    "BB6.Agent25Raw43Canonical38DirectConditional.conditional_exact_at_champion",
]

def sh(*args):
    return subprocess.check_output(args, text=True).strip()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--canonical38-run", type=int, required=True)
    a = ap.parse_args()

    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

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
        f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{a.canonical38_run}"
    ))
    assert meta["conclusion"] == "success"
    assert meta["event"] == "workflow_dispatch"
    assert meta["path"] == ".github/workflows/agent3-canonical38-direct.yml"

    downloaded = work / "direct38"
    subprocess.run([
        "gh", "run", "download", str(a.canonical38_run),
        "-n", "canonical38-raw39-raw47-direct-delta", "-D", str(downloaded)
    ], check=True)

    receipts = list(downloaded.rglob("delta.json"))
    assert len(receipts) == 1, receipts
    receipt = json.loads(receipts[0].read_text())
    delta = receipts[0].parent
    assert receipt["source_revision"] == meta["head_sha"]
    assert receipt["previous_residual_count"] == 40
    assert receipt["remaining_residual_count"] == 38
    assert receipt["exact_at_champion_score"] == (
        "BB6.Agent3Canonical38Raw39Raw47Direct.exact_at_champion_score")

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

    root, profiles = c.u.compile_one(
        HERE / "Raw43Canonical38DirectConditional.lean",
        linked, evidence, TARGETS)
    assert set(TARGETS) <= set(profiles), (set(TARGETS) - set(profiles), profiles)
    assert all(set(ax) <= ALLOWED for ax in profiles.values()), profiles
    shutil.copy2(root, evidence / root.name)

    out = {
        "claim": "source-checked conditional Raw43 removal from authenticated direct Canonical38 lineage",
        "source_revision": sh("git", "rev-parse", "HEAD"),
        "canonical38_run": a.canonical38_run,
        "canonical38_head_sha": meta["head_sha"],
        "canonical38_receipt": receipt,
        "remaining_residual_count_if_raw43_cover_supplied": 37,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": c.a68.sha(root),
        "previous_delta": pin40,
    }
    (evidence / "raw43-after-direct38-conditional.json").write_text(
        json.dumps(out, indent=2, sort_keys=True) + "\n")
    print("PASS: authenticated direct Canonical38 has Raw43 once; conditional successor has 37 Covers", flush=True)

if __name__ == "__main__":
    main()
