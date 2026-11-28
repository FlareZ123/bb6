#!/usr/bin/env python3
"""Source-check Raw42 membership/removal on an already rebuilt Canonical37."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import shutil
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
NS = "BB6.Agent10Raw42AfterCanonical37Conditional"
TARGETS = [
    NS + ".parent_count37",
    NS + ".count36",
    NS + ".removed_parent_absent",
    NS + ".conditional_sound",
    NS + ".conditional_exact_at_champion",
]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    base = work / "canonical37"
    predecessor_path = (
        base / "evidence" / "canonical37-raw47-after-raw112.json"
    )
    assert predecessor_path.is_file(), predecessor_path
    predecessor = json.loads(predecessor_path.read_text(encoding="utf-8"))
    assert predecessor["remaining_residual_count"] == 37
    assert predecessor["exact_at_champion_score"] == (
        "BB6.Agent17Raw47AfterRaw112Integrated.exact_at_champion_score"
    )

    linked = base / "canonical"
    assert (linked / "Raw47AfterRaw112Integrated.olean").is_file(), linked

    evidence = work / "evidence"
    evidence.mkdir(exist_ok=True)
    root, profiles = a25.a17.raw39.source_check(
        HERE / "Raw42AfterCanonical37Conditional.lean",
        linked,
        evidence,
        TARGETS,
    )
    assert set(TARGETS) <= set(profiles), set(TARGETS) - set(profiles)
    assert all(set(ax) <= ALLOWED for ax in profiles.values()), profiles

    source_revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
    ).strip()
    report = {
        "claim": (
            "source-checked conditional Raw42 removal from the authenticated "
            "Raw39 -> Raw112 -> Raw47 Canonical37 lineage"
        ),
        "source_revision": source_revision,
        "previous_residual_count": 37,
        "remaining_residual_count_if_raw42_cover_supplied": 36,
        "raw42_parent_table": (
            "1RB---_1RC---_0RD---_1LD0LB_------_------"
        ),
        "raw42_parent_cover_status": "explicit premise; not discharged here",
        "predecessor": predecessor,
        "axioms": profiles,
        "root": root.name,
        "root_sha256": a25.sha(root),
        "exact_at_champion_score": NS + ".conditional_exact_at_champion",
    }
    out = evidence / "raw42-after-canonical37-conditional.json"
    out.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "PASS: authenticated Canonical37 contains Raw42 exactly once; "
        "conditional successor has 36 Covers",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
