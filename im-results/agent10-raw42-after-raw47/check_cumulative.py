#!/usr/bin/env python3
"""Source-check cumulative Raw42+Raw43 conditional removal on Canonical37."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
A25 = HERE.parent / "agent25-raw43"

_spec = importlib.util.spec_from_file_location(
    "a25_raw43_after_canonical37",
    A25 / "check_canonical37_after_raw47.py",
)
a25 = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(a25)

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NS = "BB6.Agent10Raw42Raw43Canonical35Conditional"
TARGETS = [
    NS + ".p43_count36",
    NS + ".count35",
    NS + ".raw43_removed",
    NS + ".raw42_remains_removed",
    NS + ".conditional_sound",
    NS + ".conditional_exact_at_champion",
]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    predecessor_path = (
        work / "canonical37" / "evidence"
        / "canonical37-raw47-after-raw112.json"
    )
    raw42_path = (
        work / "evidence" / "raw42-after-canonical37-conditional.json"
    )
    assert predecessor_path.is_file(), predecessor_path
    assert raw42_path.is_file(), raw42_path
    predecessor = json.loads(predecessor_path.read_text(encoding="utf-8"))
    raw42 = json.loads(raw42_path.read_text(encoding="utf-8"))
    assert predecessor["remaining_residual_count"] == 37
    assert raw42["remaining_residual_count_if_raw42_cover_supplied"] == 36

    linked = work / "canonical37" / "canonical"
    assert (linked / "Raw47AfterRaw112Integrated.olean").is_file()
    assert (linked / "Raw42AfterCanonical37Conditional.olean").is_file()

    evidence = work / "evidence"
    root, profiles = a25.a17.raw39.source_check(
        HERE / "Raw42Raw43Canonical35Conditional.lean",
        linked,
        evidence,
        TARGETS,
    )
    assert set(TARGETS) <= set(profiles), set(TARGETS) - set(profiles)
    assert all(set(ax) <= ALLOWED for ax in profiles.values()), profiles

    report = {
        "claim": (
            "source-checked cumulative conditional removal of Raw42 then Raw43 "
            "from authenticated Canonical37"
        ),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
        ).strip(),
        "previous_residual_count": 37,
        "remaining_residual_count_if_raw42_and_raw43_covers_supplied": 35,
        "raw42_parent_table": "1RB---_1RC---_0RD---_1LD0LB_------_------",
        "raw43_parent_table": "1RB---_1RC---_0RD---_1LD0RB_------_------",
        "parent_cover_status": "both explicit premises; neither discharged here",
        "predecessor": predecessor,
        "raw42_conditional": raw42,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": a25.sha(root),
        "exact_at_champion_score": NS + ".conditional_exact_at_champion",
    }
    out = evidence / "raw42-raw43-after-canonical37-conditional.json"
    out.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "PASS: Canonical37 supports cumulative Raw42+Raw43 conditional cut; "
        "35 Covers remain if both parent Covers are supplied",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
