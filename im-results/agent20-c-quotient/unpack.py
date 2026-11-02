"""Recover the kernel-checked quotient transition proof with SHA-256 validation."""
from pathlib import Path
import base64
import fcntl
import hashlib
import lzma
import os
import tempfile

directory = Path(__file__).resolve().parent
expected = "1a17976a9690bd4951f2bfe3e843ba6262341d84dfcbef06a5728f81bcbccd24"
data = lzma.decompress(base64.b64decode((directory / "QuotientArithmetic.lean.xz.b64").read_text().strip()))
assert hashlib.sha256(data).hexdigest() == expected, "Lean source checksum mismatch"
target = directory / "QuotientArithmetic.lean"
with (directory / ".unpack.lock").open("a+b") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    with tempfile.NamedTemporaryFile(dir=directory, delete=False) as f:
        f.write(data)
        temporary = f.name
    os.replace(temporary, target)
    fcntl.flock(lock, fcntl.LOCK_UN)
print(f"Verified {target.name}: {len(data)} bytes; sha256 {expected}")
