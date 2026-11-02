"""Restore the SHA-256-checked Lean source with a locked atomic replacement."""
import base64
import fcntl
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "C31.lean"
EXPECTED = "dd79b36e6288787f2f83d3b3be40061323790735369e78c3d3be437594d154e6"

with (ROOT / ".reconstruct.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raw = lzma.decompress(base64.b64decode((ROOT / "C31.lean.xz.b64").read_bytes()))
    actual = hashlib.sha256(raw).hexdigest()
    if actual != EXPECTED:
        raise ValueError(f"C31 source checksum mismatch: {actual}")
    fd, name = tempfile.mkstemp(prefix=".C31.", suffix=".tmp", dir=ROOT)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        os.replace(name, SOURCE)
    finally:
        if os.path.exists(name):
            os.unlink(name)
print(f"Verified {SOURCE}: {len(raw)} bytes; SHA-256 {actual}")
