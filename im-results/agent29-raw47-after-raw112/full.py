#!/usr/bin/env python3
"""Authenticate and kernel-transport accepted Raw47 after accepted Raw112.

Prerequisites: same work directory has first passed Agent10 accepted Raw112
consumer and Agent29's conditional Raw47 roster source check. The explicit
bridge consumes the independently source-accepted Raw47 parent, rather than
adding any axiom to the theorem environment.
"""
import argparse
import json
import shutil
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "agent32-raw42"))
sys.path.insert(0, str(HERE.parent / "agent50-raw47-canonical41"))
import check_canonical39_after_raw39 as raw39
import consume_after_canonical40 as raw47

NS = "BB6.Agent29Raw47AfterRaw112"
REQUIRED = [
    NS + ".literal_eq_accepted_parent",
    NS + ".p47_source_cover",
    NS + ".sound_integrated",
    NS + ".count37",
    NS + ".exact_at_champion_score",
]

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--raw47-run-id", type=int, default=46068688341)
    p.add_argument(
        "--resume-from", type=Path,
        help="authenticated raw47-kernel-replay checkpoint from a prior workflow run",
    )
    a = p.parse_args()
    if a.resume_from is not None:
        a.resume_from = a.resume_from.resolve()
        assert (a.resume_from / "report.json").is_file(), a.resume_from
        assert (a.resume_from / "objects").is_dir(), a.resume_from
    work = a.work.resolve()
    evidence = work / "evidence"
    assert a.raw47_run_id == 46068688341, "pin the exact accepted Raw47 run"
    prior_path = evidence / "raw47-conditional-after-raw112-canonical37.json"
    assert prior_path.is_file(), "first source-check the authentic 38->37 conditional cut"
    prior = json.loads(prior_path.read_text())
    assert prior["remaining_residual_count_conditional_on_raw47_cover"] == 37
    roots = list(work.rglob("Raw47Canonical37ConditionalAfterRaw112.olean"))
    assert len(roots) == 1, [str(x) for x in roots]
    linked = roots[0].parent

    # The accepted Raw112 parent object family was already copied into the
    # common linked kernel environment. Reclaim its redundant download tree
    # before restoring the independent large Raw47 proof archive.
    assert (linked / "Raw112ClosedCover.olean").is_file()
    shutil.rmtree(work / "raw112-parent", ignore_errors=True)

    parent_work = work / "raw47-parent"
    parent_work.mkdir(exist_ok=False)
    spec, dirs = raw47.c.restore_parent(a.raw47_run_id, parent_work, evidence)
    assert spec["theorem"] == "BB6.Agent50Raw47Complete.cover"
    assert spec["table"] == "1RB---_1RC---_0RD---_1LD0RC_------_------"
    audit = {}
    copied = []
    raw47.kernel_replay_raw47(
        spec, dirs, linked, copied, audit, work, evidence,
        chunked=True, resume_from=a.resume_from)
    assert (linked / "Raw47KernelBridge.olean").is_file()
    # All kernel-reached producer roots and their import paths were checked.
    # The final source lemma also establishes definitionally exact parent
    # identity and checks the final universal Cover interface.
    root, profiles = raw39.source_check(
        HERE / "Raw47Canonical37AfterRaw112.lean", linked, evidence, REQUIRED)
    report = {
        "status": "source-checked unconditional Raw47 removal after Raw112 Canonical38",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "previous_residual_count": 38,
        "remaining_residual_count": 37,
        "raw47_accepted_run_id": a.raw47_run_id,
        "raw47_accepted_parent": spec,
        "raw47_transport": audit,
        "source_sha256": raw39.sha(HERE / "Raw47Canonical37AfterRaw112.lean"),
        "root_olean_sha256": raw39.sha(root),
        "exact_at_champion_score": NS + ".exact_at_champion_score",
        "theorems": profiles,
    }
    out = evidence / "raw47-after-raw112-canonical37.json"
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("PASS: Raw39 + Raw112 + Raw47 original-source Canonical37; "
          "all 37 remaining Covers are explicit hypotheses", flush=True)

if __name__ == "__main__":
    main()
