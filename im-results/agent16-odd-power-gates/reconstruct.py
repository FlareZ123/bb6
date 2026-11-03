"""Reconstruct independently compiled all-exponent Sheep power-gate source."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "OddPredecessor.lean.xz.b64"
DEST = ROOT / "OddPredecessor.lean"
ARCHIVE_SHA256 = "11c726827b83f756cd1a86db32a9248a959450a373710be2f14cdfece4843235"
SOURCE_SHA256 = "d1efc3e75d8002384dc079b4e68cc9229a56d7e566e2505954c16c761f7747a2"


def checked(data: bytes, expected: str) -> None:
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"SHA256 mismatch: {actual} != {expected}")


def main() -> None:
    with FileLock(str(DEST) + ".lock"):
        archive = base64.b64decode(ARCHIVE.read_text(encoding="ascii"), validate=False)
        checked(archive, ARCHIVE_SHA256)
        source = lzma.decompress(archive)
        checked(source, SOURCE_SHA256)
        with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as temp:
            path = Path(temp.name)
            temp.write(source)
            temp.flush()
            os.fsync(temp.fileno())
        try:
            os.replace(path, DEST)
        finally:
            path.unlink(missing_ok=True)
        print(f"Recovered {DEST.name} with verified SHA256 {SOURCE_SHA256}")


if __name__ == "__main__":
    main()
