"""Consume Raw120 in the accepted eleven-parent core, without regenerating children."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent31-shared-core"))
from assemble_canonical68 import (REPO, api_json, download, link_reachable,
                                  compile_module, gate, sha)

PINS = [
    (15078085872, 45732489302, "0e7b0932a1c6e35c2716dac560bb6352a6da3ade63b1376cf3660c909bf94e61"),
    (15080392441, 45733198942, "617e0e6e523edfe5bdbba757d812e2139555f054e9d4a857ccfee54d685a2364"),
]
REVISIONS = {
    45732489302: "4ad59d8689c0b5201bcff53554c5057ecab39b6d",
    45733198942: "e8dbaab36366b8282388cff6eda45fb550372774",
}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    work = ap.parse_args().work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version
    for run, rev in REVISIONS.items():
        info = api_json(f"repos/{REPO}/actions/runs/{run}")
        assert info["head_sha"] == rev and info["conclusion"] == "success", info
    groups = [download(pin, work) for pin in PINS]
    linked = work / "linked"
    link_reachable(groups, work, linked, families=[
        ("canonical65", groups[0], ["Canonical65Integrated"]),
        ("raw120", groups[1], ["Raw120Complete", "Raw120ExactLower"]),
    ])
    source = HERE / "Canonical64Raw120Integrated.lean"
    out = linked / "Canonical64Raw120Integrated.olean"
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = compile_module(source, out, env, work / "canonical64.log")
    required = ["BB6.Agent3Canonical64Raw120." + n for n in [
        "raw120_exact", "p120_root", "p120_count", "count64",
        "sound64_integrated", "exact_at_target",
    ]]
    report = {
        "pins": PINS, "source_revisions": REVISIONS,
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "lean_version": version, "source_sha256": sha(source), "olean_sha256": sha(out),
        "axioms": gate(log, required), "residual_count": 64,
        "raw120_exact_weighted_bound": 224707, "common_floor": 6766859,
    }
    (work / "canonical64-integration.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Raw120 integrated into the eleven-parent core; standard axiom gate passed.", flush=True)

if __name__ == "__main__":
    main()
