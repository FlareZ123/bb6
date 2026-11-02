"""Reconstruct and verify the two Lean-checked parity-gateway proofs.

Uses Python standard library and filelock. All writes are locked and atomic.
"""
from __future__ import annotations

import base64
import hashlib
import io
import lzma
import os
from pathlib import Path
import tarfile
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "parity-lean.tar.xz.b64"
B64_SHA256 = "8bef320f5fe325652962e9dc1719c31c5fb4f87ccac2b24a65a354adeea8e4a6"
TAR_SHA256 = "33163ffcf2a7b8fc4af0819f018aa0da6b22aa306118f81e1e9af796458df70f"
SOURCES = {
    "CParity.lean": "9d1e30042a028e55c919eb91ed4f0d343707aad3c0c928bd719f4a091d0b811a",
    "CParityGates.lean": "e478d7623fd6db1adb40c65f9c62c6fca6897660f1906188ca333d4d841b4aa9",
}


def restore() -> None:
    with FileLock(str(ROOT / ".reconstruct-parity.lock")):
        encoded = ARCHIVE.read_text(encoding="ascii").strip()
        assert hashlib.sha256(encoded.encode("ascii")).hexdigest() == B64_SHA256
        raw = lzma.decompress(base64.b64decode(encoded, validate=True))
        assert hashlib.sha256(raw).hexdigest() == TAR_SHA256

        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
            members = archive.getmembers()
            assert {m.name for m in members} == set(SOURCES)
            for name, digest in SOURCES.items():
                member = archive.getmember(name)
                assert member.isfile()
                source = archive.extractfile(member)
                assert source is not None
                data = source.read()
                assert hashlib.sha256(data).hexdigest() == digest
                with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as temp:
                    temp.write(data)
                    temp.flush()
                    os.fsync(temp.fileno())
                    temporary_path = Path(temp.name)
                os.replace(temporary_path, ROOT / name)
                print(f"Restored and verified {name} ({len(data)} bytes)")


if __name__ == "__main__":
    restore()
