"""Restore Lean-checked rational-child high-a source under hash verification."""
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
COMPRESSED_SHA256 = "f21beab20a4265cc54e7777423d334f9428cca36f5ca1c457a7055d077defc7e"
SOURCES = {
    "Sheep138ChildGenericHigh.lean": "b149d5d07583dde370b20cb6d8292a76124e004682254dbe47f85a7df6fc261c",
    "Sheep138ChildFinite.lean": "691b847f9f884c74f2d44482feb9e5a6ffe67e34c8af278e29ade37c99e1ff3a",
}

def check(data: bytes, sha: str) -> None:
    digest = hashlib.sha256(data).hexdigest()
    if digest != sha:
        raise ValueError(f"Checksum mismatch: {digest} instead of {sha}")

def restore() -> None:
    compressed = base64.b64decode((ROOT / "child138-high.tar.xz.b64").read_bytes())
    check(compressed, COMPRESSED_SHA256)
    with tarfile.open(fileobj=io.BytesIO(lzma.decompress(compressed)), mode="r:") as archive:
        if set(archive.getnames()) != set(SOURCES):
            raise ValueError("Unexpected members")
        for name, sha in SOURCES.items():
            member = archive.getmember(name)
            if not member.isfile():
                raise ValueError("Non-file member")
            input_file = archive.extractfile(member)
            if input_file is None:
                raise ValueError("Cannot read file member")
            source = input_file.read()
            check(source, sha)
            path = ROOT / name
            with FileLock(str(path) + ".lock"):
                if path.is_file() and path.read_bytes() == source:
                    print("Verified:", name)
                    continue
                fd, temporary = tempfile.mkstemp(dir=ROOT, prefix="."+name+".", suffix=".tmp")
                try:
                    with os.fdopen(fd, "wb") as output:
                        output.write(source)
                        output.flush()
                        os.fsync(output.fileno())
                    os.replace(temporary, path)
                finally:
                    if os.path.exists(temporary):
                        os.unlink(temporary)
            print("Restored:", name)

if __name__ == "__main__":
    restore()
