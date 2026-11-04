"""Reconstruct the Lean source with an atomic, locked, integrity-checked write."""
import base64
import fcntl
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parent
SOURCE = DIRECTORY / "BB429NewSix.lean.xz.b64"
OUTPUT = DIRECTORY / "BB429NewSix.lean"
SHA256 = "00ec61dedf471df1fe44151d65e5b2bca6bf1d6593e4344ce5eec194856ac460"

payload = lzma.decompress(base64.b64decode(SOURCE.read_text().strip()))
digest = hashlib.sha256(payload).hexdigest()
assert digest == SHA256, f"source checksum mismatch: {digest}"

with (DIRECTORY / ".new_six.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    if not OUTPUT.exists() or OUTPUT.read_bytes() != payload:
        with tempfile.NamedTemporaryFile(dir=DIRECTORY, delete=False) as temp:
            temp.write(payload)
            temp_name = temp.name
        os.replace(temp_name, OUTPUT)
    fcntl.flock(lock, fcntl.LOCK_UN)

print(f"Verified {OUTPUT.name}: {digest}, {len(payload)} bytes")
