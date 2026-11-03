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
ARCHIVE_SHA256 = "a654cd1fb151fb8074ac0281b849ad170b04830d2e898c46226e5541450deff0"
SOURCE_SHA256 = "db53115b1b0a6000fdf7bface4bd626e6e90221035fbfa13e8b8da3bef3d77d0"


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
