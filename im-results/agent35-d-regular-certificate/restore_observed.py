"""Restore the E ladder observational-equivalence proof atomically."""
from __future__ import annotations
import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile
from filelock import FileLock

HERE = Path(__file__).resolve().parent
FILE = HERE / "DETripleLadderObs.lean"
ARCHIVE = HERE / "DETripleLadderObs.lean.xz.b64"
SHA256 = "56459ecbfdba283d27293da9bfe5bcaa6905769b2bafe7e522d505f250784d96"

def restore() -> None:
    raw = base64.b64decode(ARCHIVE.read_text(encoding="ascii").strip(), validate=True)
    digest = hashlib.sha256(raw).hexdigest()
    if digest != SHA256:
        raise ValueError(f"Compressed-source checksum mismatch: {digest}")
    data = lzma.decompress(raw, format=lzma.FORMAT_XZ)
    with FileLock(str(HERE / ".restore.lock")):
        name = None
        try:
            with tempfile.NamedTemporaryFile(
                mode="wb", dir=HERE, prefix=".DETripleLadderObs.", delete=False
            ) as target:
                name = target.name
                target.write(data)
                target.flush()
                os.fsync(target.fileno())
            os.replace(name, FILE)
        finally:
            if name is not None and os.path.exists(name):
                os.unlink(name)
    print(f"Restored {FILE.name}: {len(data)} bytes")

if __name__ == "__main__":
    restore()
