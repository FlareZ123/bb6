#!/usr/bin/env python3
"""Rebuild accepted Canonical37 and source-check the conditional Raw43 37 -> 36 cut."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
A17 = HERE.parent / "agent17-raw47-after-raw112"

_spec = importlib.util.spec_from_file_location("a17_raw47_after_raw112", A17 / "consume.py")
a17 = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(a17)

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NS = "BB6.Agent25Raw43AfterCanonical37Conditional"
TARGETS = [
    NS + ".parent_count37",
    NS + ".count36",
    NS + ".removed_parent_absent",
    NS + ".conditional_sound",
    NS + ".conditional_exact_at_champion",
]


def sha(path: Path) -> str:
    return a17.raw39.sha(path)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw47-run-id", type=int, default=46068688341)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    base = work / "canonical37"
    subprocess.run([
        "python", str(A17 / "consume.py"),
        "--work", str(base),
        "--raw47-run-id", str(args.raw47_run_id),
        "--raw112-run-id", str(args.raw112_run_id),
        "--onele-run", str(args.onele_run),
    ], cwd=REPO, check=True)

    predecessor_path = base / "evidence" / "canonical37-raw47-after-raw112.json"
    predecessor = json.loads(predecessor_path.read_text(encoding="utf-8"))
    assert predecessor["remaining_residual_count"] == 37
    assert predecessor["exact_at_champion_score"] == (
        "BB6.Agent17Raw47AfterRaw112Integrated.exact_at_champion_score"
    )

    linked = base / "canonical"
    assert (linked / "Raw47AfterRaw112Integrated.olean").is_file(), linked

    evidence = work / "evidence"
    evidence.mkdir()
    root, profiles = a17.raw39.source_check(
        HERE / "Raw43AfterCanonical37Conditional.lean",
        linked,
        evidence,
        TARGETS,
    )
    assert set(TARGETS) <= set(profiles), set(TARGETS) - set(profiles)
    assert all(set(ax) <= ALLOWED for ax in profiles.values()), profiles
    shutil.copy2(predecessor_path, evidence / predecessor_path.name)

    source_revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
    ).strip()
    report = {
        "claim": (
            "source-checked conditional Raw43 removal from the authenticated "
            "Raw112-first / Raw47 Canonical37 lineage"
        ),
        "source_revision": source_revision,
        "previous_residual_count": 37,
        "remaining_residual_count_if_raw43_cover_supplied": 36,
        "predecessor": predecessor,
        "raw43_parent_cover_status": "explicit premise; not discharged here",
        "axioms": profiles,
        "root": root.name,
        "root_sha256": sha(root),
        "exact_at_champion_score": NS + ".conditional_exact_at_champion",
    }
    (evidence / "raw43-after-canonical37-conditional.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "PASS: authenticated Canonical37 contains Raw43 exactly once; "
        "conditional successor has 36 Covers",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
