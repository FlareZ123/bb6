#!/usr/bin/env python3
"""Consume accepted Raw83 and Raw112 together on accepted Canonical39."""
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
A31 = SIBLINGS / "agent31-shared-core"
A17 = SIBLINGS / "agent17-raw112-canonical58"
sys.path.insert(0, str(A32))
sys.path.insert(0, str(A31))
sys.path.insert(0, str(A17))

import check_canonical39_after_raw39 as raw39
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected
from assemble_canonical58_raw112_graft import verify_raw112_parent

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RAW83_SPEC = {
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
RAW112_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LC_------"
RAW112_THEOREM = "BB6.Agent47Raw112.parent_cover"
NS = "BB6.Agent10Raw83Raw112Canonical37AfterRaw39"
TARGETS = [
    NS + ".p83_count39",
    NS + ".p112_count39",
    NS + ".parents_distinct",
    NS + ".p83_cover",
    NS + ".p112_cover",
    NS + ".count37",
    NS + ".raw83_removed",
    NS + ".raw112_removed",
    NS + ".sound_integrated",
    NS + ".sound_at",
    NS + ".exact_at_champion_score",
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    # Reconstruct the exact accepted Canonical39 predecessor once.
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
        prefix="A10Raw39Raw83Raw112Slice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=args.chunk_size,
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
        namespace="A10Raw39Raw83Raw112Slice",
        compatible=(transport.get("mode") ==
                    "authenticated-original-compatible-link"),
    )
    profiles = {}
    roots = {}
    for source, targets in (
        (bridge, raw39.RAW39_BRIDGE),
        (A11 / "Raw39Canonical39Successor.lean", raw39.RAW39_SUCCESSOR),
    ):
        root, p = raw39.source_check(source, canonical, evidence, targets)
        roots[root.name] = raw39.sha(root)
        profiles.update(p)

    # Authenticate and merge the compact accepted Raw83 parent family.
    raw83_work = work / "raw83-parent"
    raw83_work.mkdir()
    raw83_dirs, raw83_meta = five.download_parent(RAW83_SPEC, raw83_work)
    raw83_copied = []
    raw83_audit = {}
    selected.add_family(
        RAW83_SPEC, raw83_dirs, canonical, raw83_copied, raw83_audit)
    assert (canonical / "A10Raw83Exact.olean").is_file()

    # Authenticate and merge the complete source-accepted Raw112 parent family.
    raw112_work = work / "raw112-parent"
    raw112_work.mkdir()
    raw112_meta, raw112_dirs, raw112_summary = verify_raw112_parent(
        raw112_work, args.raw112_run_id)
    raw112_copied = []
    raw112_audit = {}
    selected.add_family(
        {"root": "Raw112ClosedCover"},
        raw112_dirs, canonical, raw112_copied, raw112_audit)
    assert (canonical / "Raw112ClosedCover.olean").is_file()

    source = HERE / "Raw83Raw112Canonical37AfterRaw39.lean"
    root, final_profiles = raw39.source_check(
        source, canonical, evidence, TARGETS)
    roots[root.name] = raw39.sha(root)
    profiles.update(final_profiles)
    assert all(set(axioms) <= ALLOWED for axioms in profiles.values()), profiles

    report = {
        "status": (
            "source-checked Raw83 plus Raw112 successor of accepted "
            "Raw39 Canonical39"),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "accepted_predecessor": predecessor,
        "raw39_parent": parent,
        "raw39_transport_mode": transport["mode"],
        "raw39_transport_affected_modules": transport["affected_modules"],
        "previous_residual_count": 39,
        "remaining_residual_count": 37,
        "raw83_parent": RAW83_SPEC,
        "raw83_artifact": raw83_meta,
        "raw83_link_audit": raw83_audit,
        "raw83_copied_modules": [str(p) for p in raw83_copied],
        "raw112_run_id": args.raw112_run_id,
        "raw112_artifact_name": raw112_meta["artifact_name"],
        "raw112_artifact_id": raw112_meta["artifact_id"],
        "raw112_artifact_sha256": raw112_meta["artifact_digest"],
        "raw112_parent_table": RAW112_TABLE,
        "raw112_parent_theorem": RAW112_THEOREM,
        "raw112_weighted_bound": 100000,
        "raw112_retry_summary": raw112_summary,
        "raw112_link_audit": raw112_audit,
        "raw112_copied_modules": [str(p) for p in raw112_copied],
        "theorems": profiles,
        "roots": roots,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
    }
    (evidence / "raw83-raw112-after-raw39-canonical37.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw39 Canonical39 -> Raw83 + Raw112 -> Canonical37; "
        "exactly 37 Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
