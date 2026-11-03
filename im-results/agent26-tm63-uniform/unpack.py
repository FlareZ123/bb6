"""Decode the pinned Lean source archive and verify its original bytes.

The first GitHub upload lost one character on archive line 41, so the
transcription repair below is intentional and SHA-256 checked.
"""
import base64
import gzip
import hashlib
import os
from pathlib import Path
import tempfile

DIRECTORY = Path(__file__).resolve().parent
encoded = (DIRECTORY / "UniformTM63.lean.gz.b64").read_text(encoding="ascii")
encoded = encoded.replace("CvjJ3JaZ", "CvFjJ3JaZ")
raw = gzip.decompress(base64.b64decode(encoded))
assert hashlib.sha256(raw).hexdigest() == (
    "ea3a8facf99464a982d56b8e46ab5f6391cffe092da566ae9402a97c9bfa3aa5"
)
destination = DIRECTORY / "UniformTM63.lean"
with tempfile.NamedTemporaryFile(dir=DIRECTORY, delete=False) as f:
    f.write(raw)
    intermediate = f.name
os.replace(intermediate, destination)
print(f"Verified {len(raw)} Lean bytes at {destination}")
