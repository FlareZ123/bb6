#!/usr/bin/env python3
"""Emit the two final ordinary C1 proof families using fixed witness inputs.
All search data are untrusted: generated Lean must check every residual and cut.
Run from the repository root; output directory must be outside the checkout
if it already contains same-named generated modules.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EMITTER = ROOT / "im-results/agent19-raw40-cut/emit_autopump.py"

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--branch", choices=["1LE", "1RE"], required=True)
    args = parser.parse_args()
    branch = args.branch
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    prefix = "Raw44C1" + branch + "Cut"
    generated = out / ("generated-" + branch)
    generated.mkdir(exist_ok=True)
    with (generated / ("Raw44RemainingPump" + branch + ".lean")).open("w") as stream:
        subprocess.run([sys.executable, str(EMITTER), str(HERE / (branch + "-autopump-certs.jsonl")),
                        "BB6.Agent16Raw44RemainingPump.C" + branch], check=True, stdout=stream)
    subprocess.run(["node", str(HERE / "generate_cut.cjs"), str(generated), "128", branch], check=True)
    for path in sorted(generated.glob("Raw44Cut*.lean")):
        target = generated / path.name.replace("Raw44Cut", prefix)
        target.write_text(path.read_text().replace("Raw44Cut", prefix))
        path.unlink()
    print(generated / (prefix + "Assembled.lean"))

if __name__ == "__main__":
    main()
