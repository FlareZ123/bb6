"""Atomically reconstruct the kernel-checked A3PowerFanin.lean source."""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
NAME = "A3PowerFanin.lean"
EXPECTED = "2b2ba78c1460372e73c41d78a92d6b760a1188e931f501067a7207df6064473d"
archive = (ROOT / (NAME + ".xz.b64")).read_text(encoding="ascii")
source = lzma.decompress(base64.b64decode(archive))
actual = hashlib.sha256(source).hexdigest()
if actual != EXPECTED:
    raise ValueError(f"Source checksum mismatch: {actual}")

with FileLock(str(ROOT / (NAME + ".lock"))):
    with tempfile.NamedTemporaryFile(dir=ROOT, prefix=".a3-", suffix=".lean", delete=False) as stream:
        temp = Path(stream.name)
        stream.write(source)
    os.replace(temp, ROOT / NAME)
print(f"Verified {NAME}: {len(source)} bytes, SHA256 {actual}")
