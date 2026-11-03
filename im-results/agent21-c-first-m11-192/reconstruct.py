"""Restore Agent21's exact Lean proof; locked, atomic, checksum-verified."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
INPUT = ROOT / "FirstM11.lean.xz.b64"
OUTPUT = ROOT / "FirstM11.lean"
SHA256 = "e12563a3f68b46167bd967df22afd5bc46c274652e37d7f17524ea2db154890b"

with FileLock(str(OUTPUT) + ".lock"):
    source = lzma.decompress(base64.b64decode(INPUT.read_bytes()))
    actual = hashlib.sha256(source).hexdigest()
    if actual != SHA256:
        raise ValueError(f"Source SHA256 mismatch: {actual}")
    handle, name = tempfile.mkstemp(prefix=".FirstM11-", suffix=".lean", dir=ROOT)
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(source)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(name, OUTPUT)
    finally:
        if os.path.exists(name):
            os.unlink(name)
print(f"Restored {OUTPUT.name} ({len(source)} bytes), SHA256 {actual}")
