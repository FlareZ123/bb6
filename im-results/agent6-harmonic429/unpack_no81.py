"""Verify and atomically reconstruct the exact BB429No81mod512 Lean proof."""
import base64
import fcntl
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

directory = Path(__file__).resolve().parent
encoded = directory / "BB429No81mod512.lean.xz.b64"
source = directory / "BB429No81mod512.lean"
expected = "dbb54fef717c7bceb4ebe73d2b3526aa3662e8da2608356be32ecf36d80d8930"
raw = lzma.decompress(base64.b64decode(encoded.read_text().strip()))
assert hashlib.sha256(raw).hexdigest() == expected
with (directory / ".no81.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    with tempfile.NamedTemporaryFile(dir=directory, delete=False) as tmp:
        tmp.write(raw)
        tmpname = tmp.name
    os.replace(tmpname, source)
    fcntl.flock(lock, fcntl.LOCK_UN)
print("Verified BB429No81mod512.lean", len(raw), "bytes")
