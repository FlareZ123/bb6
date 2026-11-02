"""Restore and verify Agent 31's Lean 4.36.0-rc2 proof source."""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import base64
import hashlib
import lzma
import os

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "Boundary.lean.xz.b64"
OUTPUT = ROOT / "Boundary.lean"
EXPECTED = "0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883"

data = lzma.decompress(base64.b64decode(SOURCE.read_text().strip(), validate=True))
actual = hashlib.sha256(data).hexdigest()
assert actual == EXPECTED, f"Source integrity failure: {actual}"
with FileLock(str(OUTPUT) + ".lock"):
    with NamedTemporaryFile(dir=ROOT, prefix=".boundary-", delete=False) as temp:
        temp.write(data)
        temp.flush()
        os.fsync(temp.fileno())
        tmp = Path(temp.name)
    os.replace(tmp, OUTPUT)
print(f"Restored {OUTPUT} ({len(data)} bytes), sha256={actual}")
