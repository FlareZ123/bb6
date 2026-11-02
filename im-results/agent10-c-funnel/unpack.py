#!/usr/bin/env python3
"""Recover the local Lean 4.36.0-rc2 certificate, with integrity and atomic write."""
from pathlib import Path
from tempfile import NamedTemporaryFile
import base64
import hashlib
import lzma
import os

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "Funnel.lean.xz.b64"
OUTPUT = ROOT / "Funnel.lean"
SHA256 = "3094b6c7f7ba871fb6e13c10a1955e53bd4f0b6ebd410d3390e867d916225c1c"

data = lzma.decompress(base64.b64decode(ARCHIVE.read_text(encoding="ascii")))
actual = hashlib.sha256(data).hexdigest()
if actual != SHA256:
    raise ValueError(f"Lean proof integrity check failed: {actual}")

with FileLock(str(OUTPUT) + ".lock"):
    with NamedTemporaryFile(dir=ROOT, prefix=".lean-agent10-", delete=False) as temp:
        temp.write(data)
        temp.flush()
        os.fsync(temp.fileno())
        temp_path = Path(temp.name)
    os.replace(temp_path, OUTPUT)

print(f"Recovered {OUTPUT} ({len(data)} bytes, SHA-256 {actual})")
