"""Restore the checked Lean sources with exclusive lock and atomic writes."""
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

ROOT = Path(__file__).resolve().parent
ARCHIVE_SHA256 = "771b0a30dd64324a8120e65a31a6379583fee9aa6daaef68a597c5354c546275"
SOURCES = {
    "DeterministicMacro.lean": "ee3806e7d04630d9a40e239101d43cf96695e243ee3c09ac2bdc7b582172977f",
    "SheepPowerBridge.lean": "1e9da1323ce23cf4024f84544a0f0eaa34fb60c548fba347c081a9acaff42c21",
}


def verify(blob: bytes, digest: str) -> None:
    assert hashlib.sha256(blob).hexdigest() == digest, "Source SHA256 mismatch"


def main() -> None:
    with FileLock(str(ROOT / ".unpack.lock")):
        encoded = (ROOT / "formal-bridge.tar.xz.b64").read_text(encoding="ascii")
        compressed = base64.b64decode(encoded.strip(), validate=True)
        verify(compressed, ARCHIVE_SHA256)
        with tarfile.open(fileobj=io.BytesIO(lzma.decompress(compressed)), mode="r:") as archive:
            members = archive.getmembers()
            assert {m.name for m in members} == set(SOURCES)
            assert all(m.isfile() and m.name in SOURCES for m in members)
            for member in members:
                source = archive.extractfile(member)
                assert source is not None
                data = source.read()
                verify(data, SOURCES[member.name])
                with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
                    temporary = Path(tmp.name)
                    tmp.write(data)
                    tmp.flush()
                    os.fsync(tmp.fileno())
                try:
                    os.replace(temporary, ROOT / member.name)
                finally:
                    temporary.unlink(missing_ok=True)
        print("PASS: restored the two SHA256-verified Lean sources")


if __name__ == "__main__":
    main()
