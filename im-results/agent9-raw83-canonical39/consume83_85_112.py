#!/usr/bin/env python3
"""Consume source-accepted Raw83, Raw85, Raw112 on accepted Canonical39.

Unlike independently proposed roster arithmetic, this source-check reconstructs
the exact Raw39 Canonical39 predecessor from accepted proof objects, verifies
and imports the accepted four-hole Raw83 closure, and recompiles the new
unconditional Lean theorem and its transitive allowed-axiom profile.
"""
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
RAW85_SPEC = {
    "label": "raw85",
    "run_id": 45585065939,
    "revision": "52ea69fba34b5f37bbc630392d2dc6dc1d3affbe",
    "artifact_id": 15008641615,
    "artifact_name": "raw85-bound-certified",
    "digest": "a9ff7c78fb926a7a4c172b9a76c2e5a3681268943e312a3adb306930153798c7",
    "root": "Raw85Bound",
    "theorem": "BB6.Agent21Raw85.all_completions",
    "table": "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA",
    "bound": 7014,
    "size": 9435332,
}
NS = "BB6.Agent9Raw83Raw85Canonical37AfterRaw39"
NS36 = "BB6.Agent9Raw83Raw85Raw112Canonical36AfterRaw39"
TARGETS36 = [
    NS36 + ".p112_count37",
    NS36 + ".p112_cover",
    NS36 + ".count36",
    NS36 + ".raw112_removed",
    NS36 + ".sound_integrated",
    NS36 + ".exact_at_champion_score",
]
TARGETS = [
    NS + ".p83_count39",
    NS + ".p85_count39",
    NS + ".p83_p85_distinct",
    NS + ".p83_cover",
    NS + ".p85_cover",
    NS + ".count37",
    NS + ".raw83_removed",
    NS + ".raw85_removed",
    NS + ".sound_integrated",
    NS + ".exact_at_champion_score",
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    # Authenticate the original accepted Canonical40 -> Raw39 -> Canonical39
    # lineage; the resulting roster is source-elaborated, not assumed.
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
        prefix="A9Raw39Raw83Slice",
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
        namespace="A9Raw39Raw83Slice",
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

    # Reuse the source-accepted 93-module Raw83 family from the pinned
    # 2026-11-26 parent proof, not its generated/untrusted search transcript.
    raw83_work = work / "raw83-parent"
    raw83_work.mkdir()
    raw83_dirs, raw83_meta = five.download_parent(RAW83_SPEC, raw83_work)
    copied = []
    link_audit = {}
    selected.add_family(
        RAW83_SPEC, raw83_dirs, canonical, copied, link_audit)
    assert (canonical / "A10Raw83Exact.olean").is_file()

    # Transport an independent previously accepted original-source Raw85
    # 7014 Cover, verifying artifact identity and the entire kernel family.
    raw85_work = work / "raw85-parent"
    raw85_work.mkdir()
    raw85_dirs, raw85_meta = five.download_parent(RAW85_SPEC, raw85_work)
    raw85_copied = []
    raw85_audit = {}
    selected.add_family(
        RAW85_SPEC, raw85_dirs, canonical, raw85_copied, raw85_audit)
    assert (canonical / "Raw85Bound.olean").is_file()

    source = HERE / "Raw83Raw85Canonical37AfterRaw39.lean"
    root, final_profiles = raw39.source_check(
        source, canonical, evidence, TARGETS)
    roots[root.name] = raw39.sha(root)
    profiles.update(final_profiles)

    # Preserve the lightweight replay receipt and reclaim authenticated
    # temporary source bundles before downloading Raw112 (>1 GiB).
    old_report = work / "raw39-staged" / "report.json"
    if old_report.is_file():
        shutil.copy2(old_report, evidence / "raw39-transport-report.json")
    before_free = shutil.disk_usage(work).free
    for transient in (
        work / "raw39-parent", work / "raw39-staged",
        work / "raw83-parent", work / "raw85-parent",
    ):
        shutil.rmtree(transient)
    after_free = shutil.disk_usage(work).free
    print(
        f"Authenticated cleanup before Raw112: "
        f"{(after_free-before_free)//(1024**2)} MiB reclaimed; "
        f"{after_free//(1024**2)} MiB available",
        flush=True,
    )

    # Authenticate the complete 25^6 Raw112 parent proof from the accepted
    # original-source run and import the precise declaration closure into the
    # SAME Canonical39/Raw83/Raw85 environment before compiling the last cut.
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

    source36 = HERE / "Raw83Raw85Raw112Canonical36AfterRaw39.lean"
    root36, profiles36 = raw39.source_check(
        source36, canonical, evidence, TARGETS36)
    roots[root36.name] = raw39.sha(root36)
    profiles.update(profiles36)
    assert all(set(axioms) <= ALLOWED for axioms in profiles.values()), profiles

    report = {
        "status": "source-checked Raw83+Raw85+Raw112 successor of accepted Raw39 Canonical39",
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "accepted_predecessor": predecessor,
        "raw39_parent": parent,
        "raw39_transport_mode": transport["mode"],
        "raw39_transport_affected_modules": transport["affected_modules"],
        "previous_residual_count": 39,
        "remaining_residual_count": 36,
        "raw83_parent": RAW83_SPEC,
        "raw83_artifact": raw83_meta,
        "raw83_link_audit": link_audit,
        "raw83_copied_modules": [str(p) for p in copied],
        "raw85_parent": RAW85_SPEC,
        "raw85_artifact": raw85_meta,
        "raw85_link_audit": raw85_audit,
        "raw85_copied_modules": [str(p) for p in raw85_copied],
        "raw112_run_id": args.raw112_run_id,
        "raw112_parent_metadata": raw112_meta,
        "raw112_parent_summary": raw112_summary,
        "raw112_link_audit": raw112_audit,
        "raw112_copied_modules": [str(p) for p in raw112_copied],
        "theorems": profiles,
        "roots": roots,
        "exact_at_champion_score": NS36 + ".exact_at_champion_score",
    }
    (evidence / "raw83-raw85-raw112-after-raw39-canonical36.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw39 Canonical39 -> Raw83+Raw85+Raw112 "
        "-> Canonical36; exactly 36 Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
