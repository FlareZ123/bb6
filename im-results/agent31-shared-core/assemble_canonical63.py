"""Integrate Raw112 into the accepted Canonical64 quotient frontier."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import assemble_canonical68 as a68

# Canonical64's final audit artifact contains its root .olean, while its two
# accepted dependency closures are separate artifacts. Pin all three inputs.
CANONICAL65_RUN = 45732489302
CANONICAL65_REVISION = "4ad59d8689c0b5201bcff53554c5057ecab39b6d"
CANONICAL65_ARTIFACT = 15078085872
CANONICAL65_NAME = "agent31-integrated-quotient-proof-closure"
CANONICAL65_DIGEST = "0e7b0932a1c6e35c2716dac560bb6352a6da3ade63b1376cf3660c909bf94e61"
CANONICAL65_PIN = (CANONICAL65_ARTIFACT, CANONICAL65_RUN, CANONICAL65_DIGEST)

RAW120_RUN = 45733198942
RAW120_REVISION = "e8dbaab36366b8282388cff6eda45fb550372774"
RAW120_ARTIFACT = 15080392441
RAW120_NAME = "raw120-parent"
RAW120_DIGEST = "617e0e6e523edfe5bdbba757d812e2139555f054e9d4a857ccfee54d685a2364"
RAW120_PIN = (RAW120_ARTIFACT, RAW120_RUN, RAW120_DIGEST)

CANONICAL64_RUN = 45750164590
CANONICAL64_REVISION = "949fde331f10df81a968f157c622faa581597276"
CANONICAL64_ARTIFACT = 15085029091
CANONICAL64_NAME = "raw120-canonical64-audit"
CANONICAL64_DIGEST = "bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b"
CANONICAL64_PIN = (CANONICAL64_ARTIFACT, CANONICAL64_RUN, CANONICAL64_DIGEST)


def verify_pin(run_id, revision, artifact_id, name, digest):
    run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{run_id}")
    assert run["conclusion"] == "success"
    assert run["head_sha"] == revision, (run["head_sha"], revision)
    artifact = a68.api_json(f"repos/{a68.REPO}/actions/artifacts/{artifact_id}")
    assert artifact["name"] == name
    assert artifact["workflow_run"]["id"] == run_id
    assert artifact["digest"] == "sha256:" + digest
    assert not artifact["expired"]


def download_canonical64_parts(work):
    pins = [
        (CANONICAL65_RUN, CANONICAL65_REVISION, CANONICAL65_ARTIFACT,
         CANONICAL65_NAME, CANONICAL65_DIGEST, CANONICAL65_PIN),
        (RAW120_RUN, RAW120_REVISION, RAW120_ARTIFACT,
         RAW120_NAME, RAW120_DIGEST, RAW120_PIN),
        (CANONICAL64_RUN, CANONICAL64_REVISION, CANONICAL64_ARTIFACT,
         CANONICAL64_NAME, CANONICAL64_DIGEST, CANONICAL64_PIN),
    ]
    parts = {}
    for key, pin in zip(("canonical65", "raw120", "canonical64"), pins):
        run_id, revision, artifact_id, name, digest, artifact_pin = pin
        verify_pin(run_id, revision, artifact_id, name, digest)
        parts[key] = a68.download(artifact_pin, work)
    return parts


def canonical64_families(parts):
    return [
        ("canonical65", parts["canonical65"], ["Canonical65Integrated"]),
        ("raw120", parts["raw120"], ["Raw120Complete", "Raw120ExactLower"]),
        ("canonical64", parts["canonical64"], ["Canonical64Raw120Integrated"]),
    ]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw112-run-id", type=int, required=True,
                    help="successful run producing raw112-closed-parent-cover")
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version

    parts = download_canonical64_parts(work)
    raw112_meta, raw112_dirs = a68.download_named_artifact(
        args.raw112_run_id, "raw112-closed-parent-cover", work
    )

    linked = work / "linked"
    groups = [
        parts["canonical65"], parts["raw120"], parts["canonical64"], raw112_dirs
    ]
    families = canonical64_families(parts) + [
        ("raw112", raw112_dirs, ["Raw112ClosedCover"])
    ]
    a68.link_reachable(groups, work, linked, families=families)

    source = HERE / "Canonical63Raw112Integrated.lean"
    output = linked / "Canonical63Raw112Integrated.olean"
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = a68.compile_module(source, output, env, work / "canonical63.log")
    if re.search(r"sorryAx|native_decide", log):
        raise AssertionError("forbidden proof mechanism in Canonical63Raw112Integrated")

    required = [
        "BB6.Agent31Canonical63Raw112.p112_root",
        "BB6.Agent31Canonical63Raw112.p112_count",
        "BB6.Agent31Canonical63Raw112.count63",
        "BB6.Agent31Canonical63Raw112.raw112_cover",
        "BB6.Agent31Canonical63Raw112.sound63_integrated",
        "BB6.Agent31Canonical63Raw112.exact_at_target63",
    ]
    report = {
        "status": "source-audited integrated conditional 63-residual quotient interface",
        "canonical64_dependencies": {
            "canonical65": {
                "run_id": CANONICAL65_RUN, "source_revision": CANONICAL65_REVISION,
                "artifact_id": CANONICAL65_ARTIFACT, "artifact_name": CANONICAL65_NAME,
                "artifact_digest": "sha256:" + CANONICAL65_DIGEST,
            },
            "raw120": {
                "run_id": RAW120_RUN, "source_revision": RAW120_REVISION,
                "artifact_id": RAW120_ARTIFACT, "artifact_name": RAW120_NAME,
                "artifact_digest": "sha256:" + RAW120_DIGEST,
            },
            "canonical64": {
                "run_id": CANONICAL64_RUN, "source_revision": CANONICAL64_REVISION,
                "artifact_id": CANONICAL64_ARTIFACT, "artifact_name": CANONICAL64_NAME,
                "artifact_digest": "sha256:" + CANONICAL64_DIGEST,
            },
        },
        "raw112_parent": raw112_meta,
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
        "lean_version": version,
        "compiler_sha256": a68.sha(
            Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
            / "bin" / "lean"
        ),
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
        "axioms": a68.gate(log, required),
        "base_residual_count": 64,
        "raw112_parent_bound": 100000,
        "common_weighted_bound_floor": 6766859,
        "residual_count": 63,
        "remaining_obligations": (
            "a Cover at the target bound for each of the 63 retained quotient "
            "representatives, plus an attaining blank-start witness"
        ),
    }
    (work / "canonical63-integration.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(
        "Raw112 integrated into the accepted Canonical64 frontier; "
        "the 63-residual source/axiom gate passed.",
        flush=True,
    )


if __name__ == "__main__":
    main()
