"""Atomically reconstruct and SHA-256-verify Agent 23's compressed Lean proofs."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "CM16.lean": "d8ea25e4a62b5f2fe7211d7bdef1b58af6193501daf54797e10d290ed24ad516",
    "C59.lean": "12828c07852c20734f342347b32ef3b15b6e6f2307b1a2f2c48193a0303e7543",
}

for name, expected in EXPECTED.items():
    target = ROOT / name
    raw = lzma.decompress(base64.b64decode((ROOT / (name + ".xz.b64")).read_text().strip()))
    digest = hashlib.sha256(raw).hexdigest()
    if digest != expected:
        raise ValueError(f"{name} SHA-256 mismatch: {digest}")

    with FileLock(str(target) + ".lock"):
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix="." + name + "-", suffix=".tmp", delete=False) as f:
            temp_path = Path(f.name)
            f.write(raw)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_path, target)

    print(f"Restored {target.name}: {len(raw)} bytes, sha256={digest}")
