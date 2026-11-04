"""Restore exact #429 Lean certificate under a local exclusive file lock."""
import base64
import fcntl
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
NAME = "BB429No393mod512.lean"
SHA256 = "205eb810e98022eb2641dcd8ebce07fedc564064dc00dfec01faca0c68fa280e"

with (ROOT / ".unpack.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raw = lzma.decompress(base64.b64decode((ROOT / (NAME + ".xz.b64")).read_text().strip()))
    digest = hashlib.sha256(raw).hexdigest()
    if digest != SHA256:
        raise ValueError(f"Lean source SHA256 mismatch: {digest}")
    fd, temporary = tempfile.mkstemp(prefix=".lean393-", dir=ROOT)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, ROOT / NAME)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
print(f"Verified {NAME}: {len(raw)} bytes, sha256={digest}")
