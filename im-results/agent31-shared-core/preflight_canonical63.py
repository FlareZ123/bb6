"""Type-check the Canonical63 consumer against Canonical64 with an explicit Raw112 Cover stub.

This is only an integration preflight. The stub parent_cover axiom is deliberately
not source-accepted and must never be used as a mathematical result.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import assemble_canonical63 as a63

a68 = a63.a68


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version
    parts = a63.download_canonical64_parts(work)

    linked = work / "linked"
    groups = [parts["canonical65"], parts["raw120"], parts["canonical64"]]
    a68.link_reachable(
        groups, work, linked, families=a63.canonical64_families(parts)
    )
    env = dict(os.environ, LEAN_PATH=str(linked))

    stub = work / "Raw112ClosedCover.lean"
    stub.write_text("""import Canonical64Raw120Integrated
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw112
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

def parent : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,false,2⟩)

axiom parent_cover : Cover (WeightedBound 100000) parent

end BB6.Agent47Raw112
""")
    a68.compile_module(stub, linked / "Raw112ClosedCover.olean", env, work / "stub.log")

    source = HERE / "Canonical63Raw112Integrated.lean"
    output = linked / "Canonical63Raw112Integrated.olean"
    log = a68.compile_module(source, output, env, work / "canonical63-preflight.log")
    if re.search(r"sorryAx|native_decide", log):
        raise AssertionError("forbidden proof mechanism in Canonical63 preflight")

    required = [
        "BB6.Agent31Canonical63Raw112.p112_root",
        "BB6.Agent31Canonical63Raw112.p112_count",
        "BB6.Agent31Canonical63Raw112.count63",
        "BB6.Agent31Canonical63Raw112.raw112_cover",
        "BB6.Agent31Canonical63Raw112.sound63_integrated",
        "BB6.Agent31Canonical63Raw112.exact_at_target63",
    ]
    missing = [name for name in required if name not in log]
    if missing:
        raise AssertionError(f"missing theorem profiles: {missing}")
    if "BB6.Agent47Raw112.parent_cover" not in log:
        raise AssertionError("expected explicit stub parent_cover axiom not present")

    report = {
        "status": "typechecked preflight only; not an accepted parent Cover",
        "canonical64_dependencies": {
            "canonical65": {
                "run_id": a63.CANONICAL65_RUN,
                "artifact_id": a63.CANONICAL65_ARTIFACT,
                "source_revision": a63.CANONICAL65_REVISION,
            },
            "raw120": {
                "run_id": a63.RAW120_RUN,
                "artifact_id": a63.RAW120_ARTIFACT,
                "source_revision": a63.RAW120_REVISION,
            },
            "canonical64": {
                "run_id": a63.CANONICAL64_RUN,
                "artifact_id": a63.CANONICAL64_ARTIFACT,
                "source_revision": a63.CANONICAL64_REVISION,
            },
        },
        "lean_version": version,
        "stub_axiom": "BB6.Agent47Raw112.parent_cover",
        "checked_theorems": required,
        "roster_claim": "64 -> 63, conditional on the real Raw112 parent Cover",
        "source_sha256": a68.sha(source),
        "olean_sha256": a68.sha(output),
    }
    (work / "canonical63-preflight.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print("Canonical63 type-check preflight passed with the explicit parent_cover stub.", flush=True)


if __name__ == "__main__":
    main()
