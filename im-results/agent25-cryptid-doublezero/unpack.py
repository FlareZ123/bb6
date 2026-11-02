"""Reconstruct the kernel-checked TripleUniversal.lean from its compact source."""
import base64
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "TripleUniversal.lean.xz.b64"
TARGET = ROOT / "TripleUniversal.lean"
EXPECTED_SHA256 = "630ac7599e52b2daefb768e4f514e5375b9ce17b415971244f10d043a4d1a4c6"


def main() -> None:
    with FileLock(str(ROOT / ".unpack.lock")):
        contents = lzma.decompress(base64.b64decode(SOURCE.read_text(encoding="ascii")))
        digest = hashlib.sha256(contents).hexdigest()
        if digest != EXPECTED_SHA256:
            raise ValueError(f"Unexpected Lean source SHA-256: {digest}")
        if TARGET.exists() and TARGET.read_bytes() == contents:
            return
        filename = ""
        try:
            with tempfile.NamedTemporaryFile(mode="wb", dir=ROOT, prefix=".triple-", delete=False) as temp:
                filename = temp.name
                temp.write(contents)
                temp.flush()
                os.fsync(temp.fileno())
            os.replace(filename, TARGET)
        finally:
            if filename and os.path.exists(filename):
                os.unlink(filename)


if __name__ == "__main__":
    main()
