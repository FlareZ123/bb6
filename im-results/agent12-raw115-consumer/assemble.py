"""Integrate the original-source Raw115 parent into the accepted Canonical64 core."""
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

BASE = (15085029091, 45750164590,
        "bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b")
BASE_REVISION = "949fde331f10df81a968f157c622faa581597276"
RAW_RUN = 45783903926
RAW_REVISION = "9416c1292e50f47c06ae29ae4f6d2c80620e1755"

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version
    for run, rev in [(BASE[1], BASE_REVISION), (RAW_RUN, RAW_REVISION)]:
        info = api_json(f"repos/{REPO}/actions/runs/{run}")
        assert info["head_sha"] == rev and info["conclusion"] == "success", info
    artifacts = api_json(f"repos/{REPO}/actions/runs/{RAW_RUN}/artifacts?per_page=100")["artifacts"]
    roots = [a for a in artifacts if a["name"] == "raw115-certified-root" and not a["expired"]]
    assert len(roots) == 1
    raw = roots[0]
    assert raw["digest"].startswith("sha256:")
    pin = (raw["id"], RAW_RUN, raw["digest"].removeprefix("sha256:"))
    groups = [download(p, work) for p in [BASE, pin]]
    linked = work / "linked"
    link_reachable(groups, work, linked, families=[
        ("canonical64", groups[0], ["Canonical64Raw120Integrated"]),
        ("raw115", groups[1], ["Raw115Data"]),
    ])
    source = HERE / "Canonical63Raw115Integrated.lean"
    out = linked / "Canonical63Raw115Integrated.olean"
    log = compile_module(source, out, dict(os.environ, LEAN_PATH=str(linked)),
                         work / "canonical63.log")
    required = ["BB6.Agent12Canonical63Raw115." + name for name in
                ["cover115", "p115_root", "p115_count", "count63",
                 "sound63_integrated", "exact_at_target"]]
    report = {"pins": [BASE, pin], "source_revisions": [BASE_REVISION, RAW_REVISION],
              "source_revision": subprocess.check_output(["git","rev-parse","HEAD"], text=True).strip(),
              "lean_version": version, "source_sha256": sha(source),
              "olean_sha256": sha(out), "axioms": gate(log, required),
              "residual_count": 63, "raw115_weighted_bound": 7014, "common_floor": 6766859}
    (work / "canonical63-integration.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Raw115 Cover composed in the accepted canonical64 core.", flush=True)

if __name__ == "__main__":
    main()
