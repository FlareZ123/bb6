#!/usr/bin/env python3
"""Consume accepted Raw47 after the source-accepted Raw112-first Canonical38."""
import argparse
import importlib.util
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
A10 = SIBLINGS / "agent10-raw112-canonical38"
A9 = SIBLINGS / "agent9-raw112-then-raw47"
A50 = SIBLINGS / "agent50-raw47-canonical41"
sys.path.insert(0, str(A32))
sys.path.insert(0, str(A17))
sys.path.insert(0, str(A50))

import check_canonical39_after_raw39 as raw39
import assemble_canonical58_raw112_graft as raw112

spec = importlib.util.spec_from_file_location("a17_raw47_consumer", A50 / "consume.py")
raw47 = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(raw47)

# Reuse the already-audited Raw47 collision transport.  Its chunked
# trust-level-zero replay relocates incompatible declarations (for example
# SweepData) rather than weakening the exact kernel comparison.
import consume_after_canonical40 as raw47_transport

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

ACCEPTED38_RUN = 46150267242
ACCEPTED38_HEAD = "ca14c2e30428437b9ff73a1fc810972c3d32f4f4"
ACCEPTED38_ARTIFACT_ID = 15265958695
ACCEPTED38_ARTIFACT_NAME = "canonical38-raw39-raw112-accepted-delta"
ACCEPTED38_ARTIFACT_DIGEST = (
    "sha256:e0816a258cc41d77be2f225593dcb7768327fde75304e3430ccf0f505ddccd24"
)
ACCEPTED38_SOURCE_BLOB = "f09ccdbdb1a4fa6c2ad9ee1072bd5a0ad2bcbb43"

RAW112_NS = "BB6.Agent10Raw112Canonical38AfterRaw39"
RAW112_TARGETS = [
    RAW112_NS + "." + name
    for name in (
        "p112_count39", "p112_cover", "count38", "raw112_removed",
        "sound_integrated", "sound_at", "exact_at_champion_score",
    )
]
COND_NS = "BB6.Agent9Raw47AfterRaw112Conditional"
COND_TARGETS = [
    COND_NS + "." + name
    for name in (
        "p47_count38", "count37", "raw47_removed",
        "raw112_remains_removed", "conditional_sound",
        "conditional_exact_at_champion_score",
    )
]
FINAL_NS = "BB6.Agent17Raw47AfterRaw112Integrated"
FINAL_TARGETS = [
    FINAL_NS + "." + name
    for name in (
        "raw47_literal_agreement", "raw47_cover", "sound_integrated",
        "sound_at", "exact_at_champion_score",
    )
]


def authenticate_accepted38(evidence: Path):
    run = raw47.a68.api_json(
        f"repos/FlareZ123/bb6/actions/runs/{ACCEPTED38_RUN}"
    )
    assert run["conclusion"] == "success", run["conclusion"]
    assert run["head_sha"] == ACCEPTED38_HEAD, run["head_sha"]
    artifacts = raw47.a68.api_json(
        f"repos/FlareZ123/bb6/actions/runs/{ACCEPTED38_RUN}/artifacts"
    )["artifacts"]
    matches = [
        item for item in artifacts
        if item["id"] == ACCEPTED38_ARTIFACT_ID and not item["expired"]
    ]
    assert len(matches) == 1, matches
    item = matches[0]
    assert item["name"] == ACCEPTED38_ARTIFACT_NAME, item["name"]
    assert item["digest"] == ACCEPTED38_ARTIFACT_DIGEST, item["digest"]

    source = A10 / "Raw112Canonical38AfterRaw39.lean"
    blob = subprocess.check_output(
        ["git", "hash-object", str(source)], cwd=REPO, text=True
    ).strip()
    assert blob == ACCEPTED38_SOURCE_BLOB, (blob, ACCEPTED38_SOURCE_BLOB)

    receipt = {
        "run_id": ACCEPTED38_RUN,
        "head_sha": ACCEPTED38_HEAD,
        "artifact_id": ACCEPTED38_ARTIFACT_ID,
        "artifact_name": ACCEPTED38_ARTIFACT_NAME,
        "artifact_digest": ACCEPTED38_ARTIFACT_DIGEST,
        "source_blob": ACCEPTED38_SOURCE_BLOB,
        "remaining_residual_count": 38,
        "theorem": RAW112_NS + ".exact_at_champion_score",
    }
    (evidence / "accepted-canonical38-raw112-first.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    )
    return receipt


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw47-run-id", type=int, default=46068688341)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    a = ap.parse_args()

    work = a.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()
    accepted38 = authenticate_accepted38(evidence)

    # Rebuild the exact accepted Raw39 Canonical39 source environment.
    canonical, predecessor = raw39.canonical_source(work / "canonical")
    parent_linked, parent = raw39.accepted_parent(
        work / "raw39-parent", a.onele_run
    )
    assert parent["bound"] == 28311 and len(parent["producers"]) == 11

    tool = raw39.compile_stage_kernel(work, canonical)
    transport, staged_objects, staged_names = raw39.relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),
        base=canonical,
        work=work / "raw39-staged",
        root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A17Raw39Raw112Raw47Slice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=a.chunk_size,
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
        namespace="A17Raw39Raw112Raw47Slice",
        compatible=(
            transport.get("mode") ==
            "authenticated-original-compatible-link"
        ),
    )

    profiles = {}
    roots = {}
    for source, targets in (
        (bridge, raw39.RAW39_BRIDGE),
        (A11 / "Raw39Canonical39Successor.lean", raw39.RAW39_SUCCESSOR),
    ):
        root, current = raw39.source_check(
            source, canonical, evidence, targets
        )
        roots[root.name] = raw39.sha(root)
        profiles.update(current)

    # Keep only the linked canonical copies before loading the large parents.
    shutil.rmtree(work / "raw39-parent", ignore_errors=True)
    shutil.rmtree(work / "raw39-staged", ignore_errors=True)

    # Reproduce the accepted Raw112-first Canonical38 theorem in this exact
    # environment, using the independently authenticated whole-parent artifact.
    raw112_work = work / "raw112-parent"
    raw112_work.mkdir()
    raw112_meta, raw112_dirs, raw112_summary = raw112.verify_raw112_parent(
        raw112_work, a.raw112_run_id
    )
    raw112_copied = []
    raw112_audit = {}
    raw112.selected.add_family(
        {"root": "Raw112ClosedCover"},
        raw112_dirs, canonical, raw112_copied, raw112_audit
    )
    assert (canonical / "Raw112ClosedCover.olean").is_file()

    root38, current = raw39.source_check(
        A10 / "Raw112Canonical38AfterRaw39.lean",
        canonical, evidence, RAW112_TARGETS
    )
    roots[root38.name] = raw39.sha(root38)
    profiles.update(current)
    shutil.rmtree(raw112_work, ignore_errors=True)

    # Source-check exact Raw47 membership/removal geometry on that roster38
    # before importing the independent Raw47 proof object.
    cond_root, current = raw39.source_check(
        A9 / "Raw47AfterRaw112Conditional.lean",
        canonical, evidence, COND_TARGETS
    )
    roots[cond_root.name] = raw39.sha(cond_root)
    profiles.update(current)

    raw47_work = work / "raw47-parent"
    raw47_work.mkdir()
    raw47_spec, raw47_dirs = raw47.restore_parent(
        a.raw47_run_id, raw47_work, evidence
    )
    raw47_copied = []
    raw47_audit = {}
    raw47_transport.kernel_replay_raw47(
        raw47_spec, raw47_dirs, canonical, raw47_copied, raw47_audit,
        work, evidence, chunked=True
    )
    assert (canonical / "Raw47KernelBridge.olean").is_file()
    shutil.rmtree(raw47_work, ignore_errors=True)

    # Compile the same integration theorem against the relocated, independently
    # replayed Raw47 bridge.  The literal table agreement and the global
    # Canonical38 geometry are rechecked in this exact environment.
    relocated = work / "Raw47AfterRaw112Integrated.lean"
    text = (HERE / "Raw47AfterRaw112Integrated.lean").read_text()
    assert "import Raw47Complete" in text
    assert "BB6.Agent50Raw47Depth3Cut.parent" in text
    assert "BB6.Agent50Raw47Complete.cover_at" in text
    text = text.replace("import Raw47Complete", "import Raw47KernelBridge")
    text = text.replace(
        "BB6.Agent50Raw47Depth3Cut.parent",
        "BB6.Agent50Raw47Bridge.parent",
    )
    text = text.replace(
        "BB6.Agent50Raw47Complete.cover_at",
        "BB6.Agent50Raw47Bridge.cover_at",
    )
    relocated.write_text(text)

    final_root, current = raw39.source_check(
        relocated, canonical, evidence, FINAL_TARGETS
    )
    roots[final_root.name] = raw39.sha(final_root)
    profiles.update(current)

    assert all(set(ax) <= ALLOWED for ax in profiles.values()), profiles

    report = {
        "status": (
            "source-checked Raw47 successor of accepted Raw112-first Canonical38"
        ),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
        ).strip(),
        "accepted_canonical38": accepted38,
        "accepted_predecessor": predecessor,
        "raw39_parent": parent,
        "raw39_transport_mode": transport["mode"],
        "previous_residual_count": 38,
        "remaining_residual_count": 37,
        "raw112_run_id": a.raw112_run_id,
        "raw112_artifact_id": raw112_meta["artifact_id"],
        "raw112_artifact_sha256": raw112_meta["artifact_digest"],
        "raw112_retry_summary": raw112_summary,
        "raw112_link_audit": raw112_audit,
        "raw47_run_id": a.raw47_run_id,
        "raw47_parent": raw47_spec,
        "raw47_link_audit": raw47_audit,
        "axioms": profiles,
        "roots": roots,
        "exact_at_champion_score": FINAL_NS + ".exact_at_champion_score",
    }
    (evidence / "canonical37-raw47-after-raw112.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(
        "PASS: accepted Raw39 -> Raw112 -> Raw47 lineage source-checks; "
        "exactly 37 Cover obligations remain",
        flush=True,
    )


if __name__ == "__main__":
    main()
