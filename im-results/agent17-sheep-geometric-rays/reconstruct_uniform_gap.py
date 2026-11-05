"""Restore SHA256-verified Lean source from the repository archive."""
import base64
import hashlib
import lzma
import os
import tempfile
from pathlib import Path
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "UniformValuationGap.lean.xz.b64"
TARGET = ROOT / "UniformValuationGap.lean"
SHA256 = "ad7783945cc6559f103d50c9c1fba61aece3a79e345cfc81d9bba0ca4782e77c"

def reconstruct() -> Path:
    payload = lzma.decompress(base64.b64decode(ARCHIVE.read_text(encoding="ascii")))
    digest = hashlib.sha256(payload).hexdigest()
    if digest != SHA256:
        raise ValueError(f"source checksum mismatch: {digest}")
    with FileLock(str(TARGET) + ".lock"):
        with tempfile.NamedTemporaryFile(dir=ROOT, suffix=".tmp", delete=False) as f:
            f.write(payload)
            f.flush()
            os.fsync(f.fileno())
            temp = Path(f.name)
        os.replace(temp, TARGET)
    return TARGET

if __name__ == "__main__":
    print(reconstruct())
