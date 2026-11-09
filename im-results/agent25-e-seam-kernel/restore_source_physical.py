"""Reconstruct and authenticate the original-source to physical-tape bridge proof."""
from pathlib import Path
from tempfile import NamedTemporaryFile
import base64
import hashlib
import lzma
import os
import sys
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "SourcePhysicalTransfer.lean.xz.b64"
SHA256 = "83b5728dcdf3c943e0dbf5ae0e5f1d280ca095f1bb5a6342534e3af714823ee1"

def restore(destination: Path) -> None:
    content = lzma.decompress(base64.b64decode(SOURCE.read_text().strip(), validate=True))
    digest = hashlib.sha256(content).hexdigest()
    if digest != SHA256:
        raise ValueError(f"SourcePhysicalTransfer integrity error: {digest}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with FileLock(str(destination) + ".lock"):
        with NamedTemporaryFile(dir=destination.parent, prefix=".source-physical-", delete=False) as tmp:
            tmp.write(content)
            tmp.flush()
            os.fsync(tmp.fileno())
            tmp_path = tmp.name
        os.replace(tmp_path, destination)
    print(f"Restored {destination}; {len(content)} bytes; SHA256 {digest}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python restore_source_physical.py OUTPUT_DIRECTORY")
    restore(Path(sys.argv[1]) / "SourcePhysicalTransfer.lean")
