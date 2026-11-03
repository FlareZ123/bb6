"""Restore the source-verified root 138 Lean certificate, atomically and under locks."""
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
ARCHIVE = ROOT / "root138-lean.tar.xz.b64"
ARCHIVE_SHA256 = "7d04563403974f70067a496a51ddf2b77a23e06ba5bb8a9bda2a371ca7cfbb9a"
SOURCES = {
    "Sheep138LowResidues.lean": "6e4453abccacc7f8d23cc53bb5a4bf21029d1e89e3a15cd65c1638cc34ed57db",
    "Sheep138RootParents.lean": "392e19f2629a6764530a9583ebfb935e7aa321404cfa73b917ed8a340c99bcb5",
    "Sheep138RootCases.lean": "80b0f435e8919e0fad247177232bd8ffd175bfa19d656404efeea7c89f66dcb8",
    "Sheep138RootTwoChildren.lean": "d7fdbd8cd41e5e61802c60ef3334754ddfc2ba96277cfaa53af740cd22423ca4",
}

def verify(data: bytes, digest: str) -> None:
    actual = hashlib.sha256(data).hexdigest()
    if actual != digest:
        raise ValueError(f"SHA256 mismatch {actual}; expected {digest}")

def restore() -> None:
    compressed = base64.b64decode(ARCHIVE.read_bytes())
    verify(compressed, ARCHIVE_SHA256)
    raw = lzma.decompress(compressed)
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
        if set(archive.getnames()) != set(SOURCES):
            raise ValueError("Unexpected source names")
        for name, digest in SOURCES.items():
            member = archive.getmember(name)
            if not member.isfile():
                raise ValueError(f"Invalid source member: {name}")
            handle = archive.extractfile(member)
            if handle is None:
                raise ValueError(f"Unreadable source member: {name}")
            data = handle.read()
            verify(data, digest)
            destination = ROOT / name
            with FileLock(str(destination) + ".lock"):
                if destination.is_file() and destination.read_bytes() == data:
                    print("Verified unchanged:", name)
                    continue
                fd, temporary = tempfile.mkstemp(dir=ROOT, prefix=f".{name}.", suffix=".tmp")
                try:
                    with os.fdopen(fd, "wb") as output:
                        output.write(data)
                        output.flush()
                        os.fsync(output.fileno())
                    os.replace(temporary, destination)
                finally:
                    if os.path.exists(temporary):
                        os.unlink(temporary)
            print("Restored and verified:", name)

if __name__ == "__main__":
    restore()
