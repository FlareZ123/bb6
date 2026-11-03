"""Restore both checksum-verified Lean proofs of the raw/zipper semantic bridge."""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import base64
import hashlib
import lzma
import os

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "RawBoundaryBridge.lean": "fd2e8553d8efcd662208e231d5e12b2fd8efce9f78d6a6ff9ffc4c001df54892",
    "RawBoundaryHalt.lean": "9e931dc1726f209fa3e5b3bd5f65c17b59c02fde282ecb090fe42a6691605ac1",
}

for name, expected in SOURCES.items():
    output = ROOT / name
    archive = ROOT / f"{name}.xz.b64"
    data = lzma.decompress(base64.b64decode(archive.read_text().strip(), validate=True))
    actual = hashlib.sha256(data).hexdigest()
    assert actual == expected, f"{name}: SHA256 mismatch: {actual}"
    with FileLock(str(output) + ".lock"):
        with NamedTemporaryFile(dir=ROOT, prefix=f".{name}-", delete=False) as tmp:
            tmp.write(data)
            tmp.flush()
            os.fsync(tmp.fileno())
            temp_name = tmp.name
        os.replace(temp_name, output)
    print(f"Restored {output} ({len(data)} bytes), SHA256={actual}")
