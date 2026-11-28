#!/usr/bin/env python3
"""Source-accept Raw83 as a direct successor of the accepted Canonical40.

The consumer authenticates the exact Raw57 Canonical40 predecessor and the
independently accepted Raw83 parent artifact, links the Raw83 proof closure,
then compiles the 40 -> 39 quotient theorem and audits its transitive axioms.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
sys.path.insert(0, str(SIBLINGS / "agent50-raw47-canonical41"))
sys.path.insert(0, str(SIBLINGS / "agent31-shared-core"))

import consume as c
import consume_after_canonical40 as raw47
import assemble_canonical59_five_parent as five

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NS = "BB6.Agent17Canonical39Raw83"
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
NAMES = [
    NS + ".parent_count40",
    NS + ".parent_root",
    NS + ".source_cover",
    NS + ".count39",
    NS + ".removed_parent_absent",
    NS + ".sound_integrated",
    NS + ".exact_at_target",
    NS + ".exact_at_champion_score",
]


def main():
    work = Path(os.environ.get("AGENT17_WORK", "/tmp/a17-canonical39-raw83")).resolve()
    work.mkdir(parents=True, exist_ok=False)
    delta = work / "canonical39-raw83-delta"
    evidence = delta / "evidence"
    objects = delta / "objects"
    evidence.mkdir(parents=True)
    objects.mkdir()

    linked, _, _, base_report = c.base.verify_base(work, c.base.BASE_RUN)
    sharp = c.resume.restore_sharp(work, linked, base_report)
    ready, _, ready_pin = c.extra.restore_ready(work, linked, sharp, 46031670976)
    assert ready["remaining_residual_count"] == 46
    prior41, pin41 = c.restore_extra(work, linked, ready, ready_pin)
    assert prior41["remaining_residual_count"] == 41
    prior40, pin40 = raw47.restore_canonical40(work, linked, prior41, pin41)
    assert prior40["remaining_residual_count"] == 40

    parent_work = work / "raw83"
    parent_work.mkdir()
    dirs, metadata = five.download_parent(RAW83, parent_work)
    copied, audit = [], {}
    c.selected.add_family(RAW83, dirs, linked, copied, audit)

    source = HERE / "Canonical39Raw83.lean"
    root, profiles = c.u.compile_one(source, linked, evidence, NAMES)
    assert set(profiles) == set(NAMES), (set(NAMES) - set(profiles))
    assert all(set(ax) <= ALLOWED for ax in profiles.values()), profiles
    copied.append(root)

    hashes = {}
    for src in copied:
        dest = objects / src.name
        if dest.exists():
            assert c.a68.sha(dest) == c.a68.sha(src), src.name
        else:
            shutil.copy2(src, dest)
        hashes[dest.name] = c.a68.sha(dest)

    report = {
        "status": "source-accepted Raw83 successor of Canonical40",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True).strip(),
        "previous_delta": pin40,
        "previous_root_sha256": prior40["root_sha256"],
        "previous_residual_count": 40,
        "remaining_residual_count": 39,
        "parent": metadata,
        "link_audit": audit,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": hashes[root.name],
        "delta_objects": hashes,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
    }
    (delta / "delta.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print("PASS: Raw83 consumed on accepted Canonical40; 39 Covers remain",
          flush=True)


if __name__ == "__main__":
    main()
