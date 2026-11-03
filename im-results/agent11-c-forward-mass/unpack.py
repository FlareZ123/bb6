"""Verify and atomically unpack the locally Lean-checked Machine C certificate.

Requires Python 3.11+ on Linux (the supplied Lean toolchain target).
No network or extra packages. Refuses unexpected archive members.
"""
from __future__ import annotations

import base64
import fcntl
import hashlib
import io
import lzma
import os
from pathlib import Path
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "proof-src.tar.xz.b64"
ARCHIVE_SHA256 = "b164c31ba78fb0d87452d581478f16574e78889e0405eee97e38e3267922f415"
EXPECTED = frozenset(
    ["Core.lean", "Mass.lean", "MassCross.lean", "Final.lean",
     "SourceBridgeOriginal.lean"] + [f"TracePart{i}.lean" for i in range(8)]
)


def main() -> None:
    with (ROOT / ".unpack.lock").open("a+b") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        archive = base64.b64decode(ARCHIVE.read_bytes(), validate=False)
        digest = hashlib.sha256(archive).hexdigest()
        if digest != ARCHIVE_SHA256:
            raise ValueError(f"Archive SHA256 mismatch: {digest}")
        data = lzma.decompress(archive)
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:") as src:
            members = src.getmembers()
            if {m.name for m in members} != EXPECTED or any(not m.isfile() for m in members):
                raise ValueError("Unexpected archive members")
            for member in members:
                payload = src.extractfile(member).read()
                fd, temp_name = tempfile.mkstemp(prefix="." + member.name, dir=ROOT)
                try:
                    with os.fdopen(fd, "wb") as dst:
                        dst.write(payload)
                        dst.flush()
                        os.fsync(dst.fileno())
                    os.replace(temp_name, ROOT / member.name)
                finally:
                    if os.path.exists(temp_name):
                        os.unlink(temp_name)
            print(f"Verified SHA256 {digest}, extracted {len(members)} Lean sources")


if __name__ == "__main__":
    main()
