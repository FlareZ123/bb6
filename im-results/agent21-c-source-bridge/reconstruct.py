"""Restore and hash-verify Agent 21's exact Lean predecessor sources.

Compressed solely to make concurrent GitHub API commits small.
Requires Python filelock. Every write is atomic under a common lock.
"""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "CBack.lean": "84767aed6924f78e7aae1bc483a92f5aa068ccbb8f12fcfd888fa13777819474",
    "CMod32.lean": "52f852d6468489fe6bf5f1fb8963a8ed8ab49d6ea43a811862bf8787c1e9f086",
    "CMod128Six.lean": "6a2ea646e079638cd0f4c2dffc3abc0930da8a5ee9af97ffda11489f1dea80e3",
}

with FileLock(str(ROOT / ".agent21-lean-sources.lock")):
    for name, digest in SOURCES.items():
        encoded = "".join((ROOT / (name + ".xz.b64")).read_text(encoding="ascii").split())
        data = lzma.decompress(base64.b64decode(encoded, validate=True))
        actual = hashlib.sha256(data).hexdigest()
        if actual != digest:
            raise ValueError(f"{name}: SHA-256 mismatch: {actual}")
        with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
            tmp.write(data)
            tmp.flush()
            os.fsync(tmp.fileno())
            tmpname = tmp.name
        os.replace(tmpname, ROOT / name)
        print(f"Restored {name}: {len(data)} bytes, SHA-256 {digest}")
