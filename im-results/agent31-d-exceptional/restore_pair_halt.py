"""Restore the pinned Lean proof from its checked LZMA archive atomically."""
import base64
import hashlib
import lzma
import os
from pathlib import Path

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ENCODED = ROOT / "EPairHalt.lean.xz.b64"
DEST = ROOT / "EPairHalt.lean"
EXPECTED_SHA256 = "f88d195ca970879989428c5f9beda41700d045e36cea6b4df8b6005c25a79c1c"

content = lzma.decompress(base64.b64decode(ENCODED.read_text(encoding="ascii")))
actual = hashlib.sha256(content).hexdigest()
if actual != EXPECTED_SHA256:
    raise ValueError(f"EPairHalt.lean SHA256 mismatch: {actual}")
with FileLock(str(DEST) + ".lock"):
    temp = DEST.with_name(DEST.name + ".new")
    with temp.open("wb") as stream:
        stream.write(content)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temp, DEST)
print(f"Restored {DEST.name}: {len(content)} bytes, SHA256 {actual}")
