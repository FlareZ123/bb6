"""Restore the Lean proof sources from a hash-pinned archive under a file lock."""

import base64
import hashlib
import io
import lzma
import os
import tarfile
import tempfile
from pathlib import Path

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
HASHES = {
    "Agent21First219.lean": "b463032fab6742f0eebb31d509b5453f353c28e12a88c2816b33008b40365531",
    "First219Arithmetic.lean": "04340e978659e6bb29ad87238e3aa09c26368febf2bc9a85bc283f1e1f5df366",
    "Source219Bridge.lean": "2ec18ede9d914cf10aebeb177ebad760aa9f36cdc0e1a9819adfba76e4c3c39c",
}
ARCHIVE_HASH = "fd377dee63d70e863d3501a56cfc883ab8c7869205fa8c8a8b9b84dcc6ff7449"

with FileLock(str(ROOT / ".reconstruct.lock")):
    compressed = base64.b64decode((ROOT / "Agent21First219.tar.xz.b64").read_text())
    if hashlib.sha256(compressed).hexdigest() != ARCHIVE_HASH:
        raise ValueError("Archive SHA256 mismatch")
    data = lzma.decompress(compressed)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:") as archive:
        if {x.name for x in archive.getmembers()} != set(HASHES):
            raise ValueError("Unexpected archive members")
        for name, expected_sha in HASHES.items():
            source = archive.extractfile(name).read()
            if hashlib.sha256(source).hexdigest() != expected_sha:
                raise ValueError(f"Source SHA256 mismatch: {name}")
            with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
                temp_name = tmp.name
                tmp.write(source)
                tmp.flush()
                os.fsync(tmp.fileno())
            os.replace(temp_name, ROOT / name)
            print(f"verified {name} ({len(source)} bytes)")
