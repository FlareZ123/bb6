#!/usr/bin/env python3
"""Consume a source-accepted Raw42 parent on the authenticated Canonical37 lineage."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SIBLINGS = HERE.parent
A17 = SIBLINGS / "agent17-raw47-after-raw112"
A11 = SIBLINGS / "agent11-raw39"

_spec = importlib.util.spec_from_file_location(
    "a17_raw47_after_raw112",
    A17 / "consume.py",
)
a17 = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(a17)

sys.path.insert(0, str(A11))
from chunked_kernel_replay import relocate_chunked

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PARENT_THEOREM = "BB6.Agent17Raw42AcceptedParent.cover_global"
PARENT_LITERAL = "BB6.Agent17Raw42GlobalBridge.literal"
PARENT_TABLE = "1RB---_1RC---_0RD---_1LD0LB_------_------"
PARENT_BOUND = 6766859
COND_NS = "BB6.Agent10Raw42AfterCanonical37Conditional"
COND_TARGETS = [
    COND_NS + ".parent_count37",
    COND_NS + ".count36",
    COND_NS + ".removed_parent_absent",
    COND_NS + ".conditional_sound",
    COND_NS + ".conditional_exact_at_champion",
]
FINAL_NS = "BB6.Agent10Raw42Canonical36AfterRaw47"
FINAL_TARGETS = [
    FINAL_NS + ".literal_eq_accepted_parent",
    FINAL_NS + ".p42_cover",
    FINAL_NS + ".count36",
    FINAL_NS + ".sound_integrated",
    FINAL_NS + ".sound_at",
    FINAL_NS + ".exact_at_champion_score",
]


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def verify_parent(run_id: int, downloaded: Path) -> tuple[dict, dict, list[Path]]:
    run = a17.raw47.a68.api_json(
        f"repos/FlareZ123/bb6/actions/runs/{run_id}"
    )
    assert run["conclusion"] == "success", run["conclusion"]

    artifacts = a17.raw47.a68.api_json(
        f"repos/FlareZ123/bb6/actions/runs/{run_id}/artifacts"
    )["artifacts"]
    matches = [
        item for item in artifacts
        if item["name"] == "raw42-parent-compose" and not item["expired"]
    ]
    assert len(matches) == 1, matches
    item = matches[0]

    manifests = sorted(downloaded.rglob("manifest.json"))
    assert len(manifests) == 1, manifests
    manifest_path = manifests[0]
    artifact_dir = manifest_path.parent
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["schema_version"] == 1
    assert manifest["proof_source_revision"] == run["head_sha"], (
        manifest["proof_source_revision"], run["head_sha"]
    )
    assert str(manifest["workflow"]["run_id"]) == str(run_id)
    assert manifest["claim"] == {
        "theorem": PARENT_THEOREM,
        "parent_table": PARENT_TABLE,
        "weighted_bound": PARENT_BOUND,
    }
    assert manifest["artifact_name"] == "raw42-parent-certified"
    assert any(
        root["module"] == "Raw42AcceptedParent"
        for root in manifest["roots"]
    )
    assert "Lean (version 4.36.0-rc2" in manifest["lean_version"]

    objects: list[Path] = []
    modules = manifest["modules"]
    assert modules and manifest["module_count"] == len(modules)
    for entry in modules:
        rel = Path(entry["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        obj = artifact_dir / rel
        assert obj.is_file(), obj
        assert sha(obj) == entry["olean_sha256"], entry["module"]
        source = artifact_dir / (entry["module"].replace(".", "/") + ".lean")
        assert source.is_file(), source
        assert sha(source) == entry["source_sha256"], entry["module"]
        objects.append(obj)

    receipt = {
        "run_id": run_id,
        "head_sha": run["head_sha"],
        "artifact_id": item["id"],
        "artifact_name": item["name"],
        "artifact_digest": item.get("digest"),
        "manifest_sha256": sha(manifest_path),
        "module_count": len(modules),
        "theorem": PARENT_THEOREM,
        "parent_table": PARENT_TABLE,
        "weighted_bound": PARENT_BOUND,
    }
    return receipt, manifest, objects


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw42-run-id", type=int, required=True)
    ap.add_argument("--raw42-artifact-dir", type=Path, required=True)
    ap.add_argument("--raw47-run-id", type=int, default=46068688341)
    ap.add_argument("--raw112-run-id", type=int, default=46146501930)
    ap.add_argument("--onele-run", type=int, default=46114235329)
    ap.add_argument("--chunk-size", type=int, default=64)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    evidence = work / "evidence"
    evidence.mkdir()

    parent_receipt, parent_manifest, producer_objects = verify_parent(
        args.raw42_run_id, args.raw42_artifact_dir.resolve()
    )
    (evidence / "raw42-parent.json").write_text(
        json.dumps(parent_receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    canonical37 = work / "canonical37"
    subprocess.run(
        [
            "python", str(A17 / "consume.py"),
            "--work", str(canonical37),
            "--raw47-run-id", str(args.raw47_run_id),
            "--raw112-run-id", str(args.raw112_run_id),
            "--onele-run", str(args.onele_run),
        ],
        cwd=REPO,
        check=True,
    )
    predecessor = json.loads(
        (canonical37 / "evidence" / "canonical37-raw47-after-raw112.json")
        .read_text(encoding="utf-8")
    )
    assert predecessor["remaining_residual_count"] == 37
    assert predecessor["exact_at_champion_score"] == (
        "BB6.Agent17Raw47AfterRaw112Integrated.exact_at_champion_score"
    )
    linked = canonical37 / "canonical"
    assert (linked / "Raw47AfterRaw112Integrated.olean").is_file()

    cond_root, cond_profiles = a17.raw39.source_check(
        HERE / "Raw42AfterCanonical37Conditional.lean",
        linked,
        evidence,
        COND_TARGETS,
    )
    assert all(set(ax) <= ALLOWED for ax in cond_profiles.values())

    tool = a17.raw39.compile_stage_kernel(work, linked)
    report, staged_objects, names = relocate_chunked(
        producer_files=producer_objects,
        base=linked,
        work=work / "raw42-kernel-replay",
        root_module="Raw42AcceptedParent",
        root_names=[PARENT_THEOREM, PARENT_LITERAL],
        prefix="A10Raw42Slice",
        tool=tool,
        comparator_batch=A11 / "CompareKernelImportsBatch.lean",
        allow_compatible=True,
        chunk_size=args.chunk_size,
    )
    assert report["complete"]
    for obj in sorted(staged_objects.rglob("*.olean")):
        dest = linked / obj.relative_to(staged_objects)
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.exists():
            assert sha(dest) == sha(obj), dest
        else:
            shutil.copy2(obj, dest)

    compatible = (
        report.get("mode") == "authenticated-original-compatible-link"
    )
    parent_name = PARENT_LITERAL
    cover_name = PARENT_THEOREM
    if not compatible:
        if PARENT_LITERAL in names:
            parent_name = "A10Raw42Slice." + PARENT_LITERAL
        if PARENT_THEOREM in names:
            cover_name = "A10Raw42Slice." + PARENT_THEOREM

    bridge_source = work / "Raw42KernelBridge.lean"
    bridge_source.write_text(
        f"""import {report['staged_root']}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw42KernelBridge
open BB6Coverage BB6.Agent13BlankDelay
abbrev parent : PartialMachine := {parent_name}
theorem cover : Cover (WeightedBound 6766859) parent := by
  simpa only [parent] using ({cover_name})
#print axioms cover
end BB6.Agent10Raw42KernelBridge
""",
        encoding="utf-8",
    )
    bridge_root, bridge_profiles = a17.raw39.source_check(
        bridge_source,
        linked,
        evidence,
        ["BB6.Agent10Raw42KernelBridge.cover"],
    )
    assert all(set(ax) <= ALLOWED for ax in bridge_profiles.values())

    final_source = work / "Raw42Canonical36AfterRaw47.lean"
    text = (HERE / "Raw42Canonical36AfterRaw47.lean").read_text(
        encoding="utf-8"
    )
    assert "import Raw42AcceptedParent" in text
    assert PARENT_LITERAL in text
    assert PARENT_THEOREM in text
    text = text.replace(
        "import Raw42AcceptedParent", "import Raw42KernelBridge"
    )
    text = text.replace(
        PARENT_LITERAL, "BB6.Agent10Raw42KernelBridge.parent"
    )
    text = text.replace(
        PARENT_THEOREM, "BB6.Agent10Raw42KernelBridge.cover"
    )
    final_source.write_text(text, encoding="utf-8")
    final_root, final_profiles = a17.raw39.source_check(
        final_source,
        linked,
        evidence,
        FINAL_TARGETS,
    )
    assert all(set(ax) <= ALLOWED for ax in final_profiles.values())

    receipt = {
        "status": (
            "source-accepted Raw42 successor of authenticated "
            "Raw39 -> Raw112 -> Raw47 Canonical37"
        ),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
        ).strip(),
        "previous_residual_count": 37,
        "remaining_residual_count": 36,
        "predecessor": predecessor,
        "raw42_parent": parent_receipt,
        "raw42_parent_manifest_revision": parent_manifest[
            "proof_source_revision"
        ],
        "transport": {
            "mode": report["mode"],
            "staged_root": report["staged_root"],
            "affected_modules": report.get("affected_modules", []),
            "chunks": len(report.get("chunks", [])),
        },
        "conditional_root_sha256": sha(cond_root),
        "bridge_root_sha256": sha(bridge_root),
        "root": final_root.name,
        "root_sha256": sha(final_root),
        "axioms": {
            **cond_profiles,
            **bridge_profiles,
            **final_profiles,
        },
        "exact_at_champion_score": (
            FINAL_NS + ".exact_at_champion_score"
        ),
    }
    (evidence / "canonical36-raw42-after-raw47.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "PASS: source-accepted Raw42 on authenticated Canonical37; "
        "36 Covers remain",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
