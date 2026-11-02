"""Bounded experimental search for NEW Machine C reset-gateway proof candidates.

This calls the repository's existing source-certificate generator at modulus 4096
and checks whether the same generator can already discharge the parent modulo
2048. An inability to generate a proof is NOT evidence of reachability.

The generator is hash-verified and reconstructed by Agent 29's script.
"""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GENERATOR = ROOT / "im-results/agent29-c-inverse/generate_c_inverse_v2.py"


def test(modulus: int, residue: int, seconds: int) -> dict:
    with tempfile.TemporaryDirectory(prefix="a8-c-scan-") as directory:
        path = Path(directory) / "certificate.lean"
        try:
            result = subprocess.run(
                [
                    sys.executable, str(GENERATOR), str(modulus), str(residue),
                    "--output", str(path),
                ],
                timeout=seconds,
                capture_output=True,
                text=True,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return {"status": "timeout"}
        return {
            "status": "ok" if result.returncode == 0 and path.is_file()
                else f"exit={result.returncode}",
            "size": path.stat().st_size if path.is_file() else 0,
            "stderr": result.stderr[-200:] if result.returncode else "",
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=2048)
    parser.add_argument("--end", type=int, default=2112)
    parser.add_argument("--timeout", type=int, default=5)
    options = parser.parse_args()
    assert 0 <= options.start < options.end <= 4096
    print("CONTROL_2048_42", test(2048, 42, options.timeout), flush=True)
    candidates = []
    raw = []
    for residue in range(options.start, options.end):
        high = test(4096, residue, options.timeout)
        parent = test(2048, residue % 2048, options.timeout) if high["status"] == "ok" else None
        if high["status"] == "ok" and parent["status"] != "ok":
            candidates.append({"residue": residue, "child": high, "parent": parent})
        raw.append({"residue": residue, "child": high["status"],
                    "parent": None if parent is None else parent["status"]})
        if high["status"] != "ok" and residue < options.start + 3:
            print("ERROR_DETAIL", residue, json.dumps(high), flush=True)
        if residue % 8 == 0:
            print(f"Progress {residue}: {high['status']}", flush=True)
    print("EXPERIMENTAL_FINE_MODULUS_CANDIDATES", json.dumps(candidates), flush=True)
    print("EXPERIMENTAL_FINE_MODULUS_SUMMARY", json.dumps(raw), flush=True)


if __name__ == "__main__":
    main()
