"""Integrate the accepted Raw112 parent Cover into the accepted 64-roster frontier."""
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

BASE_RUN = 45750164590
BASE_REVISION = "949fde331f10df81a968f157c622faa581597276"
BASE_ARTIFACT = 15085029091
BASE_NAME = "raw120-canonical64-audit"
BASE_DIGEST = "bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b"
BASE_PIN = (BASE_ARTIFACT, BASE_RUN, BASE_DIGEST)


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

    base_run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{BASE_RUN}")
    assert base_run["conclusion"] == "success"
    assert base_run["head_sha"] == BASE_REVISION, (
        base_run["head_sha"], BASE_REVISION
    )
    base_artifact = a68.api_json(
        f"repos/{a68.REPO}/actions/artifacts/{BASE_ARTIFACT}"
    )
    assert base_artifact["name"] == BASE_NAME
    assert base_artifact["workflow_run"]["id"] == BASE_RUN
    assert base_artifact["digest"] == "sha256:" + BASE_DIGEST
    assert not base_artifact["expired"]

    base_dirs = a68.download(BASE_PIN, work)
    raw112_meta, raw112_dirs = a68.download_named_artifact(
        args.raw112_run_id, "raw112-closed-parent-cover", work
    )

    linked = work / "linked"
    groups = [base_dirs, raw112_dirs]
    families = [
        ("canonical64", base_dirs, ["Canonical64Raw120Integrated"]),
        ("raw112", raw112_dirs, ["Raw112ClosedCover"]),
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
        "base": {
            "run_id": BASE_RUN,
            "source_revision": BASE_REVISION,
            "artifact_id": BASE_ARTIFACT,
            "artifact_name": BASE_NAME,
            "artifact_digest": "sha256:" + BASE_DIGEST,
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
