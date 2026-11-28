#!/usr/bin/env python3
"""Consume source-accepted Raw83 and Raw85 on accepted Canonical39.

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
sys.path.insert(0, str(A32))
sys.path.insert(0, str(A31))

import check_canonical39_after_raw39 as raw39
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected

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
    assert all(set(axioms) <= ALLOWED for axioms in profiles.values()), profiles

    report = {
        "status": "source-checked Raw83+Raw85 successor of accepted Raw39 Canonical39",
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
        "raw83_link_audit": link_audit,
        "raw83_copied_modules": [str(p) for p in copied],
        "raw85_parent": RAW85_SPEC,
        "raw85_artifact": raw85_meta,
        "raw85_link_audit": raw85_audit,
        "raw85_copied_modules": [str(p) for p in raw85_copied],
        "theorems": profiles,
        "roots": roots,
        "exact_at_champion_score": NS + ".exact_at_champion_score",
    }
    (evidence / "raw83-raw85-after-raw39-canonical37.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "PASS: accepted Raw39 Canonical39 -> Raw83+Raw85 -> Canonical37; "
        "exactly 37 Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
