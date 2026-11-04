"""Reconstruct the pinned Lean theorem source atomically under an exclusive lock."""

import base64
import fcntl
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "ModularQuotient.lean.xz.b64"
TARGET = HERE / "ModularQuotient.lean"
EXPECTED = "93623e2fb17833129a20ed25ffc8a3765a77dad973df94c99116c54b3cbfc805"

with (HERE / ".unpack.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    source = lzma.decompress(base64.b64decode(SOURCE.read_text(encoding="ascii").strip()))
    actual = hashlib.sha256(source).hexdigest()
    if actual != EXPECTED:
        raise ValueError(f"Source SHA256 mismatch: {actual} != {EXPECTED}")
    fd, temporary = tempfile.mkstemp(prefix=".ModularQuotient-", suffix=".lean", dir=HERE)
    try:
        with os.fdopen(fd, "wb") as output:
            output.write(source)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, TARGET)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
print(f"Reconstructed {TARGET} ({len(source)} bytes), sha256 {actual}")
