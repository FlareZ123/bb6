"""Reconstruct the 86 complete Machine C reset-class Lean certificates at modulus 8192.

The earlier Agent 29 C4096 generator is itself SHA256-pinned; this module
uses its source-proved inverse rules unchanged and pins the entire output.
"""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "agent29-c4096"))
from generate_c4096 import Proof, write_atomic

GENERATOR_SHA256 = "d9bb28af7329bc21945ca9b856c8d0ee35080c10dcaa2d83f10f747264632bee"
generator = (HERE.parent / "agent29-c4096" / "generate_c4096.py").read_bytes()
assert hashlib.sha256(generator).hexdigest() == GENERATOR_SHA256, "Generator checksum mismatch"

manifest = json.loads((HERE / "manifest.json").read_text())
assert manifest["modulus"] == 8192 and len(manifest["new_residues"]) == 86
residues = manifest["new_residues"]
assert len(set(residues)) == len(residues) and all(0 <= j < 8192 for j in residues)

digest = hashlib.sha256()
rendered = []
for j in residues:
    source = Proof(j, 8192).render()
    digest.update(j.to_bytes(2, "big"))
    digest.update(source.encode("utf-8"))
    rendered.append((j, source))

assert digest.hexdigest() == manifest["aggregate_sha256"], "Certificate corpus checksum mismatch"
for j, source in rendered:
    write_atomic(HERE / f"C{j}mod8192.lean", source)
print(f"Reconstructed {len(rendered)} SHA256-checked Lean 4.36.0-rc2 proof modules")
