"""Restore the original-source E-sector Lean proof from a checksum-pinned archive."""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import base64
import hashlib
import lzma
import os
import sys

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "SourceSeamFrame.lean.xz.b64"
EXPECTED = "e65b53d0e989cc1c987ac733e07b9bdc6d0c450b74045dcb32d87aff682eb786"

def restore(destination: Path) -> None:
    data = lzma.decompress(base64.b64decode(SOURCE.read_text().strip(), validate=True))
    actual = hashlib.sha256(data).hexdigest()
    if actual != EXPECTED:
        raise ValueError(f"SourceSeamFrame integrity failure: {actual}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with FileLock(str(destination) + ".lock"):
        with NamedTemporaryFile(dir=destination.parent, prefix=".source-frame-", delete=False) as temp:
            temp.write(data)
            temp.flush()
            os.fsync(temp.fileno())
            name = temp.name
        os.replace(name, destination)
    print(f"Restored {destination}; bytes={len(data)} SHA256={actual}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python restore_source_frame.py OUTPUT_DIRECTORY")
    restore(Path(sys.argv[1]) / "SourceSeamFrame.lean")
