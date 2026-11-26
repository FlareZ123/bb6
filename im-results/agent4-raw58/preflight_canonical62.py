"""Preflight Canonical62 membership/linking with an explicit Raw112 Cover axiom stub.

This is deliberately NOT a parent-cover result. It checks the exact Raw112
parent table, Raw58 parent table, Canonical64 membership counts, the 62-entry
filter, and source/kernel compatibility before the real Raw112 Cover exists.
"""

import argparse
import json
import os
from pathlib import Path
import re

import assemble_canonical62 as a62

a63 = a62.a63
a68 = a62.a68

RAW112_RUN = 45751911115
RAW112_REVISION = "17263f8415b7ad1aa83aa08c7fb8254aa6de5507"
RAW112_ARTIFACTS = [
    (15085314343, "raw112-common-core",
     "9fc9e408c42b3a8b10126107f4c2327015d750298947fe92f801c1608aeb692b"),
    (15086587928, "raw112-shard-0",
     "0eb6bfc68292dc7aba4610eeb5fccfceb8da087599f3e73d0450527468a18998"),
]

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STUB_AXIOM = "BB6.Agent47Raw112.parent_cover"


def download_raw112_preflight(work):
    run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{RAW112_RUN}")
    assert run["head_sha"] == RAW112_REVISION, run
    dirs = []
    metadata = []
    for artifact_id, name, digest in RAW112_ARTIFACTS:
        item = a68.api_json(f"repos/{a68.REPO}/actions/artifacts/{artifact_id}")
        assert item["workflow_run"]["id"] == RAW112_RUN
        assert item["name"] == name
        assert item["digest"] == "sha256:" + digest
        assert not item["expired"]
        dirs.extend(a68.download((artifact_id, RAW112_RUN, digest), work))
        metadata.append({
            "artifact_id": artifact_id,
            "name": name,
            "digest": "sha256:" + digest,
            "updated_at": item["updated_at"],
        })
    for artifact_id, name, digest in RAW112_ARTIFACTS:
        manifests = list((work / "metadata" / str(artifact_id)).rglob("manifest.json"))
        assert manifests, f"missing {name} manifest"
        for manifest_path in manifests:
            manifest = json.loads(manifest_path.read_text())
            assert manifest["proof_source_revision"] == RAW112_REVISION
            assert "4.36.0-rc2" in manifest["lean_version"]
    return metadata, dirs


def theorem_axioms(log, theorem):
    pattern = re.compile(
        r"'" + re.escape(theorem) + r"' depends on axioms: \[(.*?)\]",
        re.DOTALL,
    )
    match = pattern.search(log)
    if not match:
        raise AssertionError(f"missing axiom profile for {theorem}")
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", match.group(1)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    version = os.popen("lean --version").read().strip()
    assert "4.36.0-rc2" in version, version

    parts = a63.download_canonical64_parts(work)
    raw112_meta, raw112_dirs = download_raw112_preflight(work)
    raw58_meta, raw58_dirs = a62.download_raw58(work)

    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        ("raw112-preflight", raw112_dirs,
         ["Raw112Data", "Raw112SiblingNever", "ResidualCover"]),
        ("raw58", raw58_dirs, ["Raw58Exact"]),
    ]
    groups = [parts["canonical65"], parts["raw120"], raw112_dirs, raw58_dirs]
    a68.link_reachable(groups, work, linked, families=families)
    env = dict(os.environ, LEAN_PATH=str(linked))

    canonical64_output, canonical64_log, canonical64_axioms = a63.compile_canonical64(
        linked, env, work
    )

    stub_source = work / "Raw112ClosedCover.lean"
    stub_source.write_text("""import Raw112Data
import Raw112SiblingNever
import ResidualCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw112
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover

/-- Preflight-only placeholder. The actual parent Cover is NOT proved here. -/
axiom parent_cover : Cover (WeightedBound 100000) parent

#print axioms parent_cover
end BB6.Agent47Raw112
""")
    stub_output = linked / "Raw112ClosedCover.olean"
    stub_log = a68.compile_module(
        stub_source, stub_output, env, work / "raw112-cover-stub.log"
    )
    if re.search(r"sorryAx|native_decide", stub_log):
        raise AssertionError("forbidden proof mechanism in Raw112 preflight stub")

    source = a62.HERE / "Canonical62Raw112Raw58Integrated.lean"
    output = linked / "Canonical62Raw112Raw58Integrated.olean"
    log = a68.compile_module(source, output, env, work / "canonical62-preflight.log")
    if re.search(r"sorryAx|native_decide", log):
        raise AssertionError("forbidden proof mechanism in Canonical62 preflight")

    names = {
        "BB6.Agent4Canonical62Raw112Raw58.p112_root": False,
        "BB6.Agent4Canonical62Raw112Raw58.p58_root": False,
        "BB6.Agent4Canonical62Raw112Raw58.parents_distinct": False,
        "BB6.Agent4Canonical62Raw112Raw58.p112_count": False,
        "BB6.Agent4Canonical62Raw112Raw58.p58_count": False,
        "BB6.Agent4Canonical62Raw112Raw58.count62": False,
        "BB6.Agent4Canonical62Raw112Raw58.raw58_cover": False,
        "BB6.Agent4Canonical62Raw112Raw58.raw112_cover": True,
        "BB6.Agent4Canonical62Raw112Raw58.sound62_integrated": True,
        "BB6.Agent4Canonical62Raw112Raw58.exact_at_target62": True,
    }
    profiles = {}
    for theorem, needs_stub in names.items():
        axioms = theorem_axioms(log, theorem)
        allowed = STANDARD_AXIOMS | ({STUB_AXIOM} if needs_stub else set())
        if not axioms <= allowed:
            raise AssertionError(f"unexpected axioms for {theorem}: {sorted(axioms)}")
        if needs_stub and STUB_AXIOM not in axioms:
            raise AssertionError(f"{theorem} unexpectedly bypasses explicit Raw112 stub")
        if not needs_stub and STUB_AXIOM in axioms:
            raise AssertionError(f"{theorem} unexpectedly depends on Raw112 stub")
        profiles[theorem] = sorted(axioms)

    report = {
        "status": "preflight only; Raw112 parent_cover is an explicit axiom stub",
        "not_a_result": True,
        "base_roster_count": 64,
        "removed_parent_count": 2,
        "preflight_roster_count": 62,
        "raw112": {
            "run_id": RAW112_RUN,
            "source_revision": RAW112_REVISION,
            "artifacts": raw112_meta,
            "stub_axiom": STUB_AXIOM,
        },
        "raw58": raw58_meta,
        "canonical64": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "source_revision": a63.CANONICAL64_REVISION,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "recompiled_olean_sha256": a68.sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "theorem_axioms": profiles,
        "lean_version": version,
        "consumer_source_sha256": a68.sha(source),
        "consumer_olean_sha256": a68.sha(output),
        "reachable_link_audit_sha256": a68.sha(work / "reachable-link-audit.json"),
        "remaining_work": "replace the explicit Raw112 parent_cover axiom with the accepted Raw112ClosedCover artifact and rerun the real Canonical62 gate",
    }
    (work / "canonical62-preflight.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print("Canonical62 preflight passed; Raw112 parent Cover remains an explicit axiom stub.", flush=True)


if __name__ == "__main__":
    main()
