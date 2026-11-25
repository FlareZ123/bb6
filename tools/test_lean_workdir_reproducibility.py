#!/usr/bin/env python3
"""Regression for path-dependent Lean object identities, using real coverage source.

Run with Lean 4.36.0-rc2 on PATH:
  python tools/test_lean_workdir_reproducibility.py

Two workspaces compile the actual BB6Coverage and an importing theorem.
The strict artifact merger may only reuse byte-identical shared objects.
"""
import argparse
import base64
import hashlib
import lzma
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
COVERAGE = ROOT / "im-results/agent13-coverage/BB6Coverage.lean.xz.b64"
EXPECTED = "fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd"
PROBE = """import BB6Coverage
namespace Probe
theorem uniqueness (step : BB6.Coverage.Config → Option BB6.Coverage.Config) {a b : Nat}
    (ha : BB6.Coverage.HaltsAt step a) (hb : BB6.Coverage.HaltsAt step b) : a = b :=
  BB6.Coverage.haltsAt_unique step ha hb
end Probe
"""

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="bb6-repro-") as tmp:
        root = Path(tmp)
        source = root / "source"
        source.mkdir()
        coverage = source / "BB6Coverage.lean"
        coverage.write_bytes(lzma.decompress(base64.b64decode(COVERAGE.read_bytes())))
        if sha(coverage) != EXPECTED:
            raise RuntimeError("authoritative BB6Coverage source checksum changed")
        probe = source / "Probe.lean"
        probe.write_text(PROBE, encoding="utf-8")
        workdirs = [root / "short", root / "longer-independent-build-directory"]
        for workdir in workdirs:
            subprocess.run([
                sys.executable, str(ROOT / "tools/lean_compile_closure.py"),
                "--workdir", str(workdir), "--jobs", "1", "--lean", args.lean,
                str(coverage), str(probe),
            ], check=True)
        for module in ("BB6Coverage", "Probe"):
            hashes = [sha(workdir / (module + ".olean")) for workdir in workdirs]
            print(module, *hashes)
            if hashes[0] != hashes[1]:
                raise RuntimeError(f"{module}: workdir-dependent compiled identity")
        print("PASS: both real coverage and downstream object are byte-identical")

if __name__ == "__main__":
    main()
