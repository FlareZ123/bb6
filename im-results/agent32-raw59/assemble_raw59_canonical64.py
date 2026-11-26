"""Strictly integrate the source-accepted Raw59 parent into Canonical64.

The published Canonical64 audit artifact contains the consumer root object.
Rebuild its complete import closure from the pinned accepted Canonical65 and
Raw120 artifacts, include the published root in the same linker family, and
require exact kernel-data comparison before composing Raw59.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))
from assemble_canonical68 import (
    REPO, api_json, download, link_reachable, compile_module, gate, sha,
)

CANONICAL64_PIN = (
    15085029091,
    45750164590,
    "bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b",
)
CANONICAL64_REVISION = "949fde331f10df81a968f157c622faa581597276"
RAW59_PARENT_TABLE = "1RB---_1RC---_0RD---_1LD1RE_---1LA_------"
RAW59_THEOREM = "BB6.Agent32Raw59UpgradeAll.bound"
RAW59_BOUND = 4200000


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler_sha = sha(prefix / "bin" / "lean")

    # Pin and verify the published Canonical64 consumer artifact.
    canonical_run = api_json(f"repos/{REPO}/actions/runs/{CANONICAL64_PIN[1]}")
    assert canonical_run["conclusion"] == "success", canonical_run
    assert canonical_run["head_sha"] == CANONICAL64_REVISION, canonical_run
    canonical64_dirs_published = download(CANONICAL64_PIN, work)
    published_roots = [
        p for directory in canonical64_dirs_published
        for p in directory.rglob("Canonical64Raw120Integrated.olean")
    ]
    assert len(published_roots) == 1, [str(p) for p in published_roots]

    # The audit artifact is intentionally thin. Reconstruct the full accepted
    # Canonical64 closure from the two exact source-accepted inputs using the
    # same pinned assembler, then compare its root against the published root.
    canonical64_base = work / "canonical64-base"
    assembler = HERE.parent / "agent3-tnf-raw120" / "assemble_raw120_canonical.py"
    subprocess.run(
        [sys.executable, str(assembler), "--work", str(canonical64_base)],
        env=os.environ.copy(),
        check=True,
    )
    rebuilt_root = canonical64_base / "linked" / "Canonical64Raw120Integrated.olean"
    assert rebuilt_root.is_file(), rebuilt_root
    canonical64_rebuilt_dirs = [canonical64_base / "linked"]
    canonical64_rebuild_report = json.loads(
        (canonical64_base / "canonical64-integration.json").read_text()
    )

    raw_run_id = int(os.environ["RAW59_PARENT_RUN_ID"])
    raw_run = api_json(f"repos/{REPO}/actions/runs/{raw_run_id}")
    assert raw_run["conclusion"] == "success", (raw_run_id, raw_run.get("conclusion"))
    artifacts = api_json(f"repos/{REPO}/actions/runs/{raw_run_id}/artifacts")["artifacts"]
    matches = [item for item in artifacts if item["name"] == "raw59-parent-certified"]
    assert len(matches) == 1, (raw_run_id, [(x["id"], x["name"]) for x in matches])
    item = matches[0]
    assert not item["expired"], (item["id"], "expired parent artifact")
    digest = item.get("digest") or ""
    assert digest.startswith("sha256:"), (item["id"], digest)
    raw59_dirs = download((item["id"], raw_run_id, digest.removeprefix("sha256:")), work)

    manifests = list((work / "metadata" / str(item["id"])).rglob("manifest.json"))
    assert len(manifests) == 1, [str(p) for p in manifests]
    parent_manifest_path = manifests[0]
    parent_manifest = json.loads(parent_manifest_path.read_text())
    claim = parent_manifest["claim"]
    assert claim["theorem"] == RAW59_THEOREM, claim
    assert claim["parent_table"] == RAW59_PARENT_TABLE, claim
    assert claim["weighted_bound"] == RAW59_BOUND, claim
    assert parent_manifest["proof_source_revision"] == raw_run["head_sha"], (
        parent_manifest["proof_source_revision"], raw_run["head_sha"]
    )
    assert "4.36.0-rc2" in parent_manifest["lean_version"], parent_manifest["lean_version"]
    assert parent_manifest["lean_binary"]["sha256"] == compiler_sha, (
        parent_manifest["lean_binary"]["sha256"], compiler_sha
    )

    linked = work / "linked"
    canonical64_published_family_dirs = [*canonical64_dirs_published, *canonical64_rebuilt_dirs]
    link_reachable(
        [canonical64_rebuilt_dirs, raw59_dirs],
        work,
        linked,
        families=[
            ("canonical64-rebuilt", canonical64_rebuilt_dirs, ["Canonical64Raw120Integrated"]),
            ("canonical64-published", canonical64_published_family_dirs,
             ["Canonical64Raw120Integrated"]),
            ("raw59-parent", raw59_dirs, ["Raw59ParentCover"]),
        ],
    )

    source = HERE / "Raw59Canonical64Integrated.lean"
    output = linked / "Raw59Canonical64Integrated.olean"
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = compile_module(source, output, env, work / "raw59-canonical64.log")
    required = [
        "BB6.Agent32Raw59Canonical64.p59_root",
        "BB6.Agent32Raw59Canonical64.p59_count",
        "BB6.Agent32Raw59Canonical64.count63",
        "BB6.Agent32Raw59Canonical64.parent_cover_at_common_floor",
        "BB6.Agent32Raw59Canonical64.sound63_integrated",
        "BB6.Agent32Raw59Canonical64.exact_at_target63",
    ]
    profiles = gate(log, required)
    report = {
        "canonical64_run_id": CANONICAL64_PIN[1],
        "canonical64_artifact_id": CANONICAL64_PIN[0],
        "canonical64_artifact_sha256": CANONICAL64_PIN[2],
        "canonical64_source_revision": CANONICAL64_REVISION,
        "canonical64_published_root_sha256": sha(published_roots[0]),
        "canonical64_rebuilt_root_sha256": sha(rebuilt_root),
        "canonical64_rebuild_report": canonical64_rebuild_report,
        "raw59_parent_run_id": raw_run_id,
        "raw59_parent_artifact_id": item["id"],
        "raw59_parent_artifact_sha256": digest.removeprefix("sha256:"),
        "raw59_parent_source_revision": raw_run["head_sha"],
        "raw59_parent_theorem": RAW59_THEOREM,
        "raw59_parent_table": RAW59_PARENT_TABLE,
        "raw59_parent_weighted_bound": RAW59_BOUND,
        "common_weighted_floor": 6766859,
        "residual_count": 63,
        "lean_version": version,
        "lean_binary_sha256": compiler_sha,
        "consumer_source_sha256": sha(source),
        "consumer_olean_sha256": sha(output),
        "axioms": profiles,
    }
    (work / "raw59-canonical64-integration.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print("Raw59 integrated into the accepted Canonical64 frontier; standard axiom gate passed.", flush=True)


if __name__ == "__main__":
    main()
