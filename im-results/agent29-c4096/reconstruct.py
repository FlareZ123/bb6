"""Restore the deterministic 85-certificate Lean generator and manifest.

The compressed bundle is byte-identical to the locally verified source,
and all writes are file-locked and atomic. See README.md for proof scope.
"""
from pathlib import Path
import base64
import fcntl
import hashlib
import io
import lzma
import os
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
XZ_SHA256 = "af2862dc04041962dc8ba9ae59c4d9e3b584adae5dbbfbcdcd40d32a5fb70f06"
EXPECTED = {
    "generate_c4096.py": "d9bb28af7329bc21945ca9b856c8d0ee35080c10dcaa2d83f10f747264632bee",
    "manifest.json": "0126adebe3ce6136c0c2e4a056db0aec0333c746978c83c9e8e9e21181f87539",
}

with (HERE / ".reconstruct.lock").open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    packed = base64.b64decode((HERE / "C4096.tar.xz.b64").read_text().strip(), validate=True)
    assert hashlib.sha256(packed).hexdigest() == XZ_SHA256, "Compressed bundle checksum mismatch"
    with tarfile.open(fileobj=io.BytesIO(lzma.decompress(packed)), mode="r:") as archive:
        assert sorted(archive.getnames()) == sorted(EXPECTED), "Unexpected archive entries"
        sources = {}
        for name, expected_hash in EXPECTED.items():
            member = archive.getmember(name)
            assert member.isfile(), name
            stream = archive.extractfile(member)
            assert stream is not None
            raw = stream.read()
            assert hashlib.sha256(raw).hexdigest() == expected_hash, name
            sources[name] = raw
    for name, raw in sources.items():
        fd, temp = tempfile.mkstemp(dir=HERE, prefix=".reconstruct-", suffix=".tmp")
        try:
            with os.fdopen(fd, "wb") as out:
                out.write(raw)
                out.flush()
                os.fsync(out.fileno())
            os.replace(temp, HERE / name)
        finally:
            if os.path.exists(temp):
                os.unlink(temp)
print("Verified both C4096 source artifacts and their immutable SHA256 hashes")
