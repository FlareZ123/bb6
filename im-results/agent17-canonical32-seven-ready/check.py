#!/usr/bin/env python3
"""Source-check the seven-ready 39 -> 32 conditional quotient on accepted Canonical39."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SIBLINGS = HERE.parent
REPO = HERE.parents[1]
A32 = SIBLINGS / "agent32-raw42"
A11 = SIBLINGS / "agent11-raw39"
sys.path.insert(0, str(A32))

import check_canonical39_after_raw39 as raw39

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NS = "BB6.Agent17Canonical32SevenReadyConditional"
TARGETS = [
    NS + "." + name
    for name in (
        "p47_count39", "p112_count39", "p106_count39", "p79_count39",
        "p67_count39", "p83_count39", "p85_count39",
        "parents_pairwise_distinct", "parents_root", "count32",
        "all_seven_removed", "conditional_sound",
        "conditional_exact_at_champion",
    )
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    canonical, predecessor = raw39.canonical_source(work / "canonical")
    parent_linked, parent = raw39.accepted_parent(
        work / "raw39-parent", args.onele_run)
    assert parent["bound"] == 28311 and len(parent["producers"]) == 11

    tool = raw39.compile_stage_kernel(work, canonical)
    transport, staged_objects, staged_names = raw39.relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=canonical,
        work=work / "raw39-staged",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A17Raw39SevenReadySlice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=args.chunk_size,
    )
    assert transport["complete"]
    assert "BB6.Agent11Raw39Closed.parent_bound" in staged_names
    for file in sorted(staged_objects.glob("*.olean")):
        dest = canonical / file.name
        if dest.exists():
            assert raw39.sha(dest) == raw39.sha(file), file.name
        else:
            shutil.copy2(file, dest)

    bridge = raw39.generated_bridge(
        work, transport["staged_root"], staged_names,
        namespace="A17Raw39SevenReadySlice",
        compatible=(
            transport.get("mode") ==
            "authenticated-original-compatible-link"
        ),
    )

    profiles = {}
    for source, targets in (
        (bridge, raw39.RAW39_BRIDGE),
        (A11 / "Raw39Canonical39Successor.lean", raw39.RAW39_SUCCESSOR),
        (HERE / "Canonical32SevenReadyConditional.lean", TARGETS),
    ):
        _, current = raw39.source_check(source, canonical, evidence, targets)
        profiles.update(current)

    assert all(set(axioms) <= ALLOWED for axioms in profiles.values()), profiles

    receipt = {
        "status": "source-checked conditional seven-ready cut on accepted Canonical39",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "previous_residual_count": 39,
        "conditional_residual_count": 32,
        "unproved_premises": [
            "Cover (WeightedBound 6766859) " + name
            for name in ("p47", "p112", "p106", "p79", "p67", "p83", "p85")
        ],
        "accepted_predecessor": predecessor,
        "raw39_parent": parent,
        "raw39_transport_mode": transport["mode"],
        "axioms": profiles,
    }
    (evidence / "seven-ready-conditional32.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Canonical39 quotient has seven distinct ready parents; "
        "conditional residual count is exactly 32",
        flush=True,
    )


if __name__ == "__main__":
    main()
