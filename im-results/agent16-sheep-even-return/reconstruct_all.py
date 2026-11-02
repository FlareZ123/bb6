"""Restore and hash-check all five self-contained Sheep even-section Lean modules.

Source archives are reproducible and check both compressed and individual
module SHA256 hashes. Writes are locked and atomic for concurrent researchers.
"""
from __future__ import annotations

import base64
import hashlib
import io
import lzma
import os
import tarfile
import tempfile
from pathlib import Path

from filelock import FileLock
from reconstruct import restore

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "even-reach-lean.tar.xz.b64"
ARCHIVE_HASH = "a80b35711d95a9dc452ebbfe8fa34c8ea0db7878d282e77bd5f179b633f22a32"
SOURCE_HASHES = {
    "EvenEdge.lean": "11e9b78ee4ddc8dca5538915d2d2773f83741643ad64eaeb6135259d0efe72b9",
    "OddPrefix.lean": "91770e9d2c51dafbc3c4255cb9a9a5cf612202f577c9192b0de47086063ea2b0",
    "EvenReach.lean": "f9a53188f50244823465e984a76b920858c2d8afc0cb42f84ff577a6687adda2",
    "BlankEven.lean": "ffbd5a35959e9593257dc63daf6051e5a26093a35b04e0a59a84475647c753d7",
}


def validate(data: bytes, digest: str) -> None:
    actual = hashlib.sha256(data).hexdigest()
    if actual != digest:
        raise ValueError(f"SHA256 mismatch: {actual}, expected {digest}")


def restore_all() -> tuple[Path, ...]:
    restore()
    compressed = base64.b64decode(ARCHIVE.read_bytes())
    validate(compressed, ARCHIVE_HASH)
    archive_bytes = lzma.decompress(compressed)
    restored: list[Path] = []
    with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:") as archive:
        names = set(archive.getnames())
        if names != set(SOURCE_HASHES):
            raise ValueError("Unexpected Lean archive members")
        for name, digest in SOURCE_HASHES.items():
            member = archive.getmember(name)
            if not member.isfile():
                raise ValueError(f"Invalid archive member: {name}")
            stream = archive.extractfile(member)
            assert stream is not None
            data = stream.read()
            validate(data, digest)
            destination = ROOT / name
            with FileLock(str(destination) + ".lock"):
                fd, temporary = tempfile.mkstemp(
                    prefix=f".{name}.", suffix=".tmp", dir=ROOT
                )
                try:
                    with os.fdopen(fd, "wb") as handle:
                        handle.write(data)
                        handle.flush()
                        os.fsync(handle.fileno())
                    os.replace(temporary, destination)
                finally:
                    if os.path.exists(temporary):
                        os.unlink(temporary)
            restored.append(destination)
    return tuple(restored)


if __name__ == "__main__":
    for path in (ROOT / "SheepEven.lean", *restore_all()):
        print(f"Restored and checked: {path}")
