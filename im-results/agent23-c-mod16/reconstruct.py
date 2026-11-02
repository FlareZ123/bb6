"""Atomically reconstruct and SHA-256-verify Agent 23's compressed Lean proof."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
TARGET = ROOT / "CM16.lean"
EXPECTED = "d8ea25e4a62b5f2fe7211d7bdef1b58af6193501daf54797e10d290ed24ad516"

raw = lzma.decompress(base64.b64decode((ROOT / "CM16.lean.xz.b64").read_text().strip()))
digest = hashlib.sha256(raw).hexdigest()
if digest != EXPECTED:
    raise ValueError(f"CM16.lean SHA-256 mismatch: {digest}")

with FileLock(str(TARGET) + ".lock"):
    with tempfile.NamedTemporaryFile(dir=ROOT, prefix=".CM16-", suffix=".tmp", delete=False) as f:
        temp_path = Path(f.name)
        f.write(raw)
        f.flush()
        os.fsync(f.fileno())
    os.replace(temp_path, TARGET)

print(f"Restored {TARGET.name}: {len(raw)} bytes, sha256={digest}")
