#!/usr/bin/env python3
"""Source-check the Raw42 37-to-36 conditional successor after Raw112 and Raw47."""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
A50 = HERE.parent / "agent50-raw47-canonical41"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(A50))

import check_canonical39_after_raw39 as raw42

TARGETS = [
    "BB6.Agent17Raw42AfterRaw112Raw47.parent_count37",
    "BB6.Agent17Raw42AfterRaw112Raw47.parent_root",
    "BB6.Agent17Raw42AfterRaw112Raw47.count36",
    "BB6.Agent17Raw42AfterRaw112Raw47.removed_parent_absent",
    "BB6.Agent17Raw42AfterRaw112Raw47.conditional_sound",
    "BB6.Agent17Raw42AfterRaw112Raw47.conditional_exact_at_champion",
]
NAMED_TARGETS = [
    "BB6.Agent17Raw42FromNamedAfterRaw47.literal_eq_p42",
    "BB6.Agent17Raw42FromNamedAfterRaw47.cover_from_named_at_global",
    "BB6.Agent17Raw42FromNamedAfterRaw47.sound_from_named",
    "BB6.Agent17Raw42FromNamedAfterRaw47.exact_from_named",
]


def main():
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    a = ap.parse_args()
    work = a.work.resolve()
    evidence = work / "evidence"
    evidence.mkdir(exist_ok=True)
    roots = list(work.rglob("Raw47Canonical37AfterRaw112.olean"))
    assert len(roots) == 1, [str(x) for x in roots]
    linked = roots[0].parent
    assert (linked / "Raw47KernelBridge.olean").is_file()
    assert (linked / "Raw47Canonical37ConditionalAfterRaw112.olean").is_file()

    profiles = {}
    roots_out = {}
    sources = [
        (HERE / "Raw42Canonical40Membership.lean",
         ["BB6.Agent17Raw42Canonical40Membership.parent_present"]),
        (HERE / "Raw42Canonical36AfterRaw112Raw47.lean", TARGETS),
        (HERE / "Raw42Canonical36FromNamed.lean", NAMED_TARGETS),
    ]
    for source, names in sources:
        root, p = raw42.source_check(source, linked, evidence, names)
        roots_out[root.name] = raw42.sha(root)
        profiles.update(p)

    receipt = {
        "claim": "source-checked Raw42 conditional removal after accepted Raw112+Raw47 Canonical37",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "predecessor": "accepted Raw39 -> Raw112 Canonical38 -> Raw47 Canonical37",
        "remaining_residual_count_if_raw42_cover_supplied": 36,
        "raw42_parent": "1RB---_1RC---_0RD---_1LD0LB_------_------",
        "raw42_parent_cover_status": "conditional on the twelve named first-level child Covers",
        "theorems": profiles,
        "roots": roots_out,
    }
    out = evidence / "raw42-after-raw112-raw47-canonical36.json"
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("PASS: Raw42 is uniquely present in the accepted Raw112+Raw47 Canonical37 roster; "
          "the conditional successor leaves 36 Covers", flush=True)


if __name__ == "__main__":
    main()
