"""Restore the independently Lean-checked Sheep even-section module.

Source is base64-encoded XZ, with both compressed and unpacked SHA256 pinned.
The destination is replaced atomically while an interprocess lock is held.
"""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "SheepEven.lean.xz.b64"
DESTINATION = ROOT / "SheepEven.lean"
COMPRESSED_HASH = "3d3e5504ae411315eb1182d74f1be6e11b82affc74fc71a022d23181cfb8162d"
SOURCE_HASH = "82d1b77cbd8d2071b624834de5796697f6d3b02941ecda08d7f0075cbea846d5"


def check_hash(payload: bytes, expected: str) -> None:
    actual = hashlib.sha256(payload).hexdigest()
    if actual != expected:
        raise ValueError(f"SHA256 mismatch: {actual} != {expected}")


def restore() -> Path:
    with FileLock(str(DESTINATION) + ".lock"):
        compressed = base64.b64decode(ARCHIVE.read_bytes(), validate=False)
        check_hash(compressed, COMPRESSED_HASH)
        source = lzma.decompress(compressed)
        check_hash(source, SOURCE_HASH)
        fd, temporary = tempfile.mkstemp(prefix=".SheepEven.", suffix=".tmp", dir=ROOT)
        try:
            with os.fdopen(fd, "wb") as stream:
                stream.write(source)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, DESTINATION)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)
    return DESTINATION


if __name__ == "__main__":
    print(f"Restored and verified: {restore()}")
