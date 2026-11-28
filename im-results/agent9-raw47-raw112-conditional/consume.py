#!/usr/bin/env python3
"""Kernel source-check the exact two-ready-parent conditional cut on accepted Canonical39."""
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

import check_canonical39_after_raw39 as accepted39

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NS = "BB6.Agent9Canonical37TwoReadyConditional"
TARGETS = [
    NS + ".p47_count39",
    NS + ".p112_count39",
    NS + ".pairwise_distinct",
    NS + ".parents_root",
    NS + ".count37",
    NS + ".raw47_removed",
    NS + ".raw112_removed",
    NS + ".conditional_sound",
    NS + ".conditional_exact_at_champion_score",
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

    # Original accepted Canonical40 modules and whole Raw39 parent, not an
    # inferred manifest count or a second independently reconstructed roster.
    canonical, predecessor = accepted39.canonical_source(work / "canonical")
    parent_linked, parent = accepted39.accepted_parent(
        work / "raw39-parent", args.onele_run)
    assert parent["bound"] == 28311
    assert len(parent["producers"]) == 11

    tool = accepted39.compile_stage_kernel(work, canonical)
    transport, objects, names = accepted39.relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=canonical,
        work=work / "raw39-staged",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A9TwoReadyRaw39Slice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=args.chunk_size,
    )
    assert transport["complete"]
    assert "BB6.Agent11Raw39Closed.parent_bound" in names
    for f in sorted(objects.glob("*.olean")):
        dest = canonical / f.name
        if dest.exists():
            assert accepted39.sha(dest) == accepted39.sha(f), f.name
        else:
            shutil.copy2(f, dest)

    bridge = accepted39.generated_bridge(
        work, transport["staged_root"], names,
        namespace="A9TwoReadyRaw39Slice",
        compatible=(transport.get("mode") ==
                    "authenticated-original-compatible-link"),
    )

    roots = {}
    profiles = {}
    for source, targets in (
        (bridge, accepted39.RAW39_BRIDGE),
        (A11 / "Raw39Canonical39Successor.lean", accepted39.RAW39_SUCCESSOR),
        (HERE / "Canonical37TwoReadyConditional.lean", TARGETS),
    ):
        root, p = accepted39.source_check(source, canonical, evidence, targets)
        roots[root.name] = accepted39.sha(root)
        profiles.update(p)
    assert all(set(v) <= ALLOWED for v in profiles.values()), profiles

    receipt = {
        "status": "source-checked conditional Raw47+Raw112 removal from accepted Canonical39",
        "note": "two explicit complete-parent Cover hypotheses remain; this is not the unconditional global Canonical37",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "accepted_predecessor": predecessor,
        "raw39_parent": parent,
        "raw39_transport_mode": transport["mode"],
        "raw39_transport_affected_modules": transport["affected_modules"],
        "previous_residual_count": 39,
        "conditionally_retained_residual_count": 37,
        "unproved_premises": [
            "Cover (WeightedBound 6766859) p47",
            "Cover (WeightedBound 6766859) p112",
        ],
        "theorems": profiles,
        "roots": roots,
        "exact_at_champion_score": NS + ".conditional_exact_at_champion_score",
    }
    (evidence / "two-ready-conditional37.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: exact accepted Canonical39 permits conditional Raw47+Raw112 cut "
        "39 -> 37; two Covers explicitly remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
