#!/usr/bin/env python3
"""Source-check the live Raw47 complement after accepted Raw39+Raw112 Canonical38.

Run only after agent10's accepted-source consumer has successfully populated
the same --work tree. This produces a conditional theorem; it does *not*
silently import or assume the Raw47 parent Cover as an established axiom.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "agent32-raw42"))
import check_canonical39_after_raw39 as raw39

NS = "BB6.Agent29Raw47AfterRaw112Conditional"
REQUIRED = [
    NS + ".p47_count38",
    NS + ".p47_root",
    NS + ".count37",
    NS + ".raw47_removed",
    NS + ".conditional_sound",
    NS + ".conditional_exact_at_champion",
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    a = parser.parse_args()
    work = a.work.resolve()
    assert (work / "evidence" / "raw112-after-raw39-canonical38.json").is_file(), (
        "accepted Raw112/Raw39 predecessor must be source-checked first")
    predecessor = json.loads(
        (work / "evidence" / "raw112-after-raw39-canonical38.json").read_text())
    assert predecessor["remaining_residual_count"] == 38
    assert predecessor["raw112_parent_theorem"] == "BB6.Agent47Raw112.parent_cover"
    assert predecessor["exact_at_champion_score"] == (
        "BB6.Agent10Raw112Canonical38AfterRaw39.exact_at_champion_score")
    candidates = list(work.rglob("Raw112Canonical38AfterRaw39.olean"))
    assert len(candidates) == 1, [str(p) for p in candidates]
    linked = candidates[0].parent
    source = HERE / "Raw47Canonical37ConditionalAfterRaw112.lean"
    root, profiles = raw39.source_check(source, linked, work / "evidence", REQUIRED)
    report = {
        "status": "source-checked conditional Raw47 removal after accepted Raw112 Canonical38",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "predecessor_remaining_residual_count": 38,
        "remaining_residual_count_conditional_on_raw47_cover": 37,
        "raw47_parent_table": "1RB---_1RC---_0RD---_1LD0RC_------_------",
        "raw47_cover_hypothesis": "Cover (WeightedBound 6766859) p47",
        "predecessor_source_revision": predecessor["source_revision"],
        "source_sha256": raw39.sha(source),
        "root_olean_sha256": raw39.sha(root),
        "theorems": profiles,
    }
    out = work / "evidence" / "raw47-conditional-after-raw112-canonical37.json"
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("PASS: Raw47 occurs exactly once after accepted Raw112; "
          "conditional 38->37 roster source checked", flush=True)

if __name__ == "__main__":
    main()
