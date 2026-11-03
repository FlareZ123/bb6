"""Restore the independently kernel-checked all-parameter E-boundary proof.

Use: python im-results/agent37-root-language-pilot/unpack_standalone.py
Then (from this directory, Lean 4.36.0-rc2):
  LEAN_PATH=. lean -o BoundaryWitness.olean BoundaryWitness.lean
  LEAN_PATH=. lean -o E110111StandaloneBase.olean E110111StandaloneBase.lean
  LEAN_PATH=. lean E110111Standalone.lean

Requires 'filelock'; all source outputs are checked before atomic replacement.
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

ROOT = Path(__file__).resolve().parent
ARCHIVE_SHA256 = "090f6e069fe70903f07f438f4e64571b35e8d60c5d99d3686d363f92303d0d72"
FILES = {
    "E110111StandaloneBase.lean": "72a3c807e13a1112f9ad1f27723202a3bfafc4ca09cefacaf3ace5f1386aecf3",
    "E110111Standalone.lean": "599df59ff3054172e49447d2e3836b2439239c2e62778110f1976ec84d7d0c29",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def restore() -> None:
    encoded = (ROOT / "E110111Standalone.tar.xz.b64").read_text(encoding="ascii")
    compressed = base64.b64decode(encoded, validate=False)
    assert sha256(compressed) == ARCHIVE_SHA256, "Compressed archive checksum mismatch"
    with tarfile.open(fileobj=io.BytesIO(lzma.decompress(compressed)), mode="r:") as archive:
        members = archive.getmembers()
        assert sorted(member.name for member in members) == sorted(FILES), "Unexpected tar member"
        contents = {}
        for member in members:
            assert member.isfile() and member.name in FILES
            readable = archive.extractfile(member)
            assert readable is not None
            payload = readable.read()
            assert sha256(payload) == FILES[member.name], f"Source checksum mismatch: {member.name}"
            contents[member.name] = payload

    with FileLock(str(ROOT / ".E110111Standalone.restore.lock")):
        for name, payload in contents.items():
            destination = ROOT / name
            tmp_path = None
            try:
                with tempfile.NamedTemporaryFile(dir=ROOT, prefix=".e110111.", suffix=".tmp", delete=False) as handle:
                    tmp_path = Path(handle.name)
                    handle.write(payload)
                    handle.flush()
                    os.fsync(handle.fileno())
                os.replace(tmp_path, destination)
                print(f"Restored {destination.name}: {sha256(payload)}")
            finally:
                if tmp_path is not None:
                    tmp_path.unlink(missing_ok=True)


if __name__ == "__main__":
    restore()
