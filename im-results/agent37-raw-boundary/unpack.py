"""Restore the verified Lean proof of the D-family raw/zipper semantic bridge."""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import base64
import hashlib
import lzma
import os

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "RawBoundaryBridge.lean.xz.b64"
OUTPUT = ROOT / "RawBoundaryBridge.lean"
EXPECTED = "fd2e8553d8efcd662208e231d5e12b2fd8efce9f78d6a6ff9ffc4c001df54892"

data = lzma.decompress(base64.b64decode(ARCHIVE.read_text().strip(), validate=True))
actual = hashlib.sha256(data).hexdigest()
assert actual == EXPECTED, f"Source integrity mismatch: {actual}"
with FileLock(str(OUTPUT) + ".lock"):
    with NamedTemporaryFile(dir=ROOT, prefix=".raw-boundary-", delete=False) as tmp:
        tmp.write(data)
        tmp.flush()
        os.fsync(tmp.fileno())
        temp_name = tmp.name
    os.replace(temp_name, OUTPUT)
print(f"Restored {OUTPUT} ({len(data)} bytes), SHA256={actual}")
