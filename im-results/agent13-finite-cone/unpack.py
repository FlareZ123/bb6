"""Reconstruct and verify the kernel-checked Lean source. Python 3, stdlib only."""
from pathlib import Path
import base64
import hashlib
import lzma
import os
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "FiniteCone.lean.xz.b64"
TARGET = ROOT / "FiniteCone.lean"
LOCK = ROOT / "FiniteCone.lean.lock"
EXPECTED = "d3da96644529df55c4aa88ad7ebf17e002fb936940e874c3ae86700b48b6ddc6"

def unpack() -> None:
    fd = os.open(LOCK, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    try:
        data = lzma.decompress(base64.b64decode(SOURCE.read_text(encoding="ascii")))
        actual = hashlib.sha256(data).hexdigest()
        if actual != EXPECTED:
            raise ValueError(f"Checksum mismatch: {actual}")
        if TARGET.exists() and TARGET.read_bytes() == data:
            print(f"Already verified: {TARGET}")
            return
        temp_fd, temp_name = tempfile.mkstemp(prefix=".FiniteCone.", suffix=".tmp", dir=ROOT)
        try:
            with os.fdopen(temp_fd, "wb") as out:
                out.write(data)
                out.flush()
                os.fsync(out.fileno())
            os.replace(temp_name, TARGET)
        finally:
            if os.path.exists(temp_name):
                os.unlink(temp_name)
        print(f"Reconstructed and verified: {TARGET}")
    finally:
        os.close(fd)
        LOCK.unlink()

if __name__ == "__main__":
    unpack()
