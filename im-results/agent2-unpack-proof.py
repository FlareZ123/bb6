#!/usr/bin/env python3
"""Recover the Lean 4.36.0-rc2 proof stored as xz-compressed base64 text."""
from pathlib import Path
from tempfile import NamedTemporaryFile
import base64
import hashlib
import lzma
import os

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "agent2-cryptid-proof.lean.xz.b64"
OUTPUT = ROOT / "agent2-cryptid-proof.lean"
SHA256 = "58e4beca8f67073460c098d43a7043a93c7a708c1d32aceff299d8bf98e3489d"

data = lzma.decompress(base64.b64decode(ARCHIVE.read_text().strip()))
actual = hashlib.sha256(data).hexdigest()
assert actual == SHA256, f"Archive integrity failed: {actual}"
with FileLock(str(OUTPUT) + ".lock"):
    with NamedTemporaryFile(dir=ROOT, prefix=".cryptid-", delete=False) as temp:
        temp.write(data)
        temp.flush()
        os.fsync(temp.fileno())
        temp_path = Path(temp.name)
    os.replace(temp_path, OUTPUT)
print(f"Recovered {OUTPUT.name}, {len(data)} bytes, SHA-256 {actual}")
