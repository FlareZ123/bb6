#!/usr/bin/env python3
"""Consume the source-accepted Raw112 parent on the accepted Raw39 Canonical39 frontier."""
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
A17 = SIBLINGS / "agent17-raw112-canonical58"
sys.path.insert(0, str(A32))
sys.path.insert(0, str(A17))

import check_canonical39_after_raw39 as raw39
import assemble_canonical58_raw112_graft as raw112

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGET_NS = "BB6.Agent10Raw112Canonical38AfterRaw39"
TARGETS = [
    TARGET_NS + ".p112_count39",
    TARGET_NS + ".p112_cover",
    TARGET_NS + ".count38",
    TARGET_NS + ".raw112_removed",
    TARGET_NS + ".sound_integrated",
    TARGET_NS + ".sound_at",
    TARGET_NS + ".exact_at_champion_score",
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    a = ap.parse_args()

    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    # Reconstruct and source-elaborate the exact accepted Raw39 Canonical39
    # lineage rather than assuming a roster count from a receipt.
    canonical, predecessor = raw39.canonical_source(work / "canonical")
    parent_linked, parent = raw39.accepted_parent(work / "raw39-parent", a.onele_run)
    assert parent["bound"] == 28311 and len(parent["producers"]) == 11

    tool = raw39.compile_stage_kernel(work, canonical)
    transport, staged_objects, staged_names = raw39.relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=canonical,
        work=work / "raw39-staged",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A10Raw39Slice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=a.chunk_size,
    )
    assert transport["complete"]
    assert "BB6.Agent11Raw39Closed.parent_bound" in staged_names
    for f in sorted(staged_objects.glob("*.olean")):
        dest = canonical / f.name
        if dest.exists():
            assert raw39.sha(dest) == raw39.sha(f), f.name
        else:
            shutil.copy2(f, dest)

    bridge = raw39.generated_bridge(
        work, transport["staged_root"], staged_names,
        namespace="A10Raw39Slice",
        compatible=(transport.get("mode") == "authenticated-original-compatible-link"),
    )
    profiles = {}
    roots = {}
    for source, targets in [
        (bridge, raw39.RAW39_BRIDGE),
        (A11 / "Raw39Canonical39Successor.lean", raw39.RAW39_SUCCESSOR),
    ]:
        root, p = raw39.source_check(source, canonical, evidence, targets)
        roots[root.name] = raw39.sha(root)
        profiles.update(p)

    # Authenticate the already source-accepted 24-branch Raw112 parent artifact,
    # then merge its exact object family into the reconstructed Canonical39
    # environment with source/import/compiler identity checks.
    raw112_work = work / "raw112-parent"
    raw112_work.mkdir()
    meta, dirs, summary = raw112.verify_raw112_parent(raw112_work, a.raw112_run_id)
    copied = []
    link_audit = {}
    raw112.selected.add_family(
        {"root": "Raw112ClosedCover"}, dirs, canonical, copied, link_audit)
    assert (canonical / "Raw112ClosedCover.olean").is_file()

    source = HERE / "Raw112Canonical38AfterRaw39.lean"
    root, p = raw39.source_check(source, canonical, evidence, TARGETS)
    roots[root.name] = raw39.sha(root)
    profiles.update(p)
    assert all(set(ax) <= ALLOWED for ax in profiles.values()), profiles

    report = {
        "status": "source-checked Raw112 successor of accepted Raw39 Canonical39",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "accepted_predecessor": predecessor,
        "raw39_parent": parent,
        "raw39_transport_mode": transport["mode"],
        "raw39_transport_affected_modules": transport["affected_modules"],
        "previous_residual_count": 39,
        "remaining_residual_count": 38,
        "raw112_run_id": a.raw112_run_id,
        "raw112_artifact_name": meta["artifact_name"],
        "raw112_artifact_id": meta["artifact_id"],
        "raw112_artifact_sha256": meta["artifact_digest"],
        "raw112_parent_table": raw112.RAW112_TABLE,
        "raw112_parent_theorem": raw112.RAW112_THEOREM,
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": summary,
        "raw112_link_audit": link_audit,
        "theorems": profiles,
        "roots": roots,
        "exact_at_champion_score": TARGET_NS + ".exact_at_champion_score",
    }
    (evidence / "raw112-after-raw39-canonical38.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw39 Canonical39 -> Raw112 -> Canonical38; "
        "exactly 38 Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
