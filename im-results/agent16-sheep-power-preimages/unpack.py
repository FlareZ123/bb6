"""Reconstruct the independent Lean 4.36.0-rc2 proof sources.

The archive contains exactly four expected source files. SHA256 verification
happens before extraction, followed by exclusive-lock atomic file replacement.
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
ARCHIVE = ROOT / "formal-lean.tar.xz.b64"
EXPECTED_COMPRESSED_SHA256 = "f0f82b40ddacaa3905dda02b8454b6efe08361c13df783dcaef354ebf075c003"
EXPECTED_TAR_SHA256 = "d989e3e6433c96f1a30cff98a324c80666df3af711912ef0c3d74f7625fe5808"
EXPECTED_FILES = {
    "ModCycle.lean": "dfd1845a8644f3a559fc1fc13d1e473c3bd1b30e1832997a6747d05542a8a160",
    "Arithmetic.lean": "4593a263e578e91d7dea52fda3bdd6eaf6a0fa65ad18d23b3106f89090e8568b",
    "Generic.lean": "accbca2d01dd9298e36e9a912cefa764b12ef08bb61ab2722573027f1ac06bb4",
    "GenericMod.lean": "c79240423d72fd959bdc2760c27db62b0e08789b98556a0515ae533024c1e1be",
}


def verify_digest(data: bytes, expected: str) -> None:
    digest = hashlib.sha256(data).hexdigest()
    if digest != expected:
        raise ValueError(f"SHA256 mismatch: expected {expected}, received {digest}")


def main() -> None:
    with FileLock(str(ROOT / ".unpack.lock")):
        compressed = base64.b64decode(ARCHIVE.read_bytes(), validate=False)
        verify_digest(compressed, EXPECTED_COMPRESSED_SHA256)
        raw = lzma.decompress(compressed)
        verify_digest(raw, EXPECTED_TAR_SHA256)
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
            members = archive.getmembers()
            assert len(members) == len(EXPECTED_FILES)
            assert set(m.name for m in members) == set(EXPECTED_FILES)
            for member in members:
                assert member.isfile()
                source = archive.extractfile(member)
                assert source is not None
                payload = source.read()
                verify_digest(payload, EXPECTED_FILES[member.name])
                fd, tmp = tempfile.mkstemp(prefix=".proof-", suffix=".tmp", dir=ROOT)
                try:
                    with os.fdopen(fd, "wb") as output:
                        output.write(payload)
                        output.flush()
                        os.fsync(output.fileno())
                    os.replace(tmp, ROOT / member.name)
                finally:
                    if os.path.exists(tmp):
                        os.unlink(tmp)
                print("Verified and restored:", member.name)


if __name__ == "__main__":
    main()
