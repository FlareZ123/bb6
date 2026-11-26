"""Compose two source-accepted E1 parent Covers directly into Canonical64.

The script reconstructs the full Canonical64 import closure from its pinned
accepted inputs, compares the published Canonical64 root, downloads and checks
both parent artifacts by run ID/digest/manifest, then performs a strict
reachable-kernel link and compiles the 62-residual consumer.
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

PARENT_SPECS = {
    "raw59": {
        "env": "RAW59_PARENT_RUN_ID",
        "artifact": "raw59-parent-certified",
        "theorem": "BB6.Agent32Raw59UpgradeAll.bound",
        "table": "1RB---_1RC---_0RD---_1LD1RE_---1LA_------",
        "bound": 4200000,
        "root": "Raw59ParentCover",
    },
    "raw112": {
        "env": "RAW112_PARENT_RUN_ID",
        "artifact": "raw112-closed-parent-cover",
        "theorem": "BB6.Agent47Raw112.parent_cover",
        "table": "1RB---_1RC---_0RD---_1LD1RE_---1LC_------",
        "bound": 100000,
        "root": "Raw112ClosedCover",
    },
}


def fetch_parent(spec, work, compiler_sha):
    run_id = int(os.environ[spec["env"]])
    run = api_json(f"repos/{REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success", (run_id, run.get("conclusion"))
    artifacts = api_json(f"repos/{REPO}/actions/runs/{run_id}/artifacts")["artifacts"]
    matches = [item for item in artifacts if item["name"] == spec["artifact"]]
    assert len(matches) == 1, (run_id, spec["artifact"], matches)
    item = matches[0]
    assert not item["expired"], (item["id"], "expired artifact")
    digest = item.get("digest") or ""
    assert digest.startswith("sha256:"), (item["id"], digest)
    dirs = download((item["id"], run_id, digest.removeprefix("sha256:")), work)
    manifests = list((work / "metadata" / str(item["id"])).rglob("manifest.json"))
    assert len(manifests) == 1, [str(p) for p in manifests]
    manifest = json.loads(manifests[0].read_text())
    claim = manifest["claim"]
    assert claim["theorem"] == spec["theorem"], claim
    assert claim["parent_table"] == spec["table"], claim
    assert claim["weighted_bound"] == spec["bound"], claim
    assert manifest["proof_source_revision"] == run["head_sha"], (
        manifest["proof_source_revision"], run["head_sha"]
    )
    assert "4.36.0-rc2" in manifest["lean_version"], manifest["lean_version"]
    assert manifest["lean_binary"]["sha256"] == compiler_sha, (
        manifest["lean_binary"]["sha256"], compiler_sha
    )
    return {
        "run_id": run_id,
        "source_revision": run["head_sha"],
        "artifact_id": item["id"],
        "artifact_name": item["name"],
        "artifact_sha256": digest.removeprefix("sha256:"),
        "theorem": spec["theorem"],
        "parent_table": spec["table"],
        "weighted_bound": spec["bound"],
        "manifest": manifest,
    }, dirs


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

    canonical_run = api_json(f"repos/{REPO}/actions/runs/{CANONICAL64_PIN[1]}")
    assert canonical_run["conclusion"] == "success", canonical_run
    assert canonical_run["head_sha"] == CANONICAL64_REVISION, canonical_run
    canonical64_published_dirs = download(CANONICAL64_PIN, work)
    published_roots = [
        p for directory in canonical64_published_dirs
        for p in directory.rglob("Canonical64Raw120Integrated.olean")
    ]
    assert len(published_roots) == 1, [str(p) for p in published_roots]

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

    raw59_meta, raw59_dirs = fetch_parent(PARENT_SPECS["raw59"], work, compiler_sha)
    raw112_meta, raw112_dirs = fetch_parent(PARENT_SPECS["raw112"], work, compiler_sha)

    linked = work / "linked"
    canonical64_published_family_dirs = [
        *canonical64_published_dirs, *canonical64_rebuilt_dirs
    ]
    link_reachable(
        [canonical64_rebuilt_dirs, raw59_dirs, raw112_dirs],
        work,
        linked,
        families=[
            ("canonical64-rebuilt", canonical64_rebuilt_dirs, ["Canonical64Raw120Integrated"]),
            ("canonical64-published", canonical64_published_family_dirs,
             ["Canonical64Raw120Integrated"]),
            ("raw59-parent", raw59_dirs, ["Raw59ParentCover"]),
            ("raw112-parent", raw112_dirs, ["Raw112ClosedCover"]),
        ],
    )

    source = HERE / "Raw59Raw112Canonical62Integrated.lean"
    output = linked / "Raw59Raw112Canonical62Integrated.olean"
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = compile_module(source, output, env, work / "raw59-raw112-canonical62.log")
    required = [
        "BB6.Agent32Raw59Raw112Canonical62.p59_root",
        "BB6.Agent32Raw59Raw112Canonical62.p112_root",
        "BB6.Agent32Raw59Raw112Canonical62.p59_count",
        "BB6.Agent32Raw59Raw112Canonical62.p112_count",
        "BB6.Agent32Raw59Raw112Canonical62.p59_p112_distinct",
        "BB6.Agent32Raw59Raw112Canonical62.count62",
        "BB6.Agent32Raw59Raw112Canonical62.p59_cover_at_common_floor",
        "BB6.Agent32Raw59Raw112Canonical62.p112_cover_at_common_floor",
        "BB6.Agent32Raw59Raw112Canonical62.parents_root",
        "BB6.Agent32Raw59Raw112Canonical62.parents_cover",
        "BB6.Agent32Raw59Raw112Canonical62.sound62_integrated",
        "BB6.Agent32Raw59Raw112Canonical62.exact_at_target62",
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
        "raw59_parent": raw59_meta,
        "raw112_parent": raw112_meta,
        "common_weighted_floor": 6766859,
        "residual_count": 62,
        "lean_version": version,
        "lean_binary_sha256": compiler_sha,
        "consumer_source_sha256": sha(source),
        "consumer_olean_sha256": sha(output),
        "axioms": profiles,
    }
    (work / "raw59-raw112-canonical62-integration.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(
        "Raw59 and Raw112 integrated into the accepted Canonical64 frontier; "
        "the 62-residual standard-axiom gate passed.",
        flush=True,
    )


if __name__ == "__main__":
    main()
