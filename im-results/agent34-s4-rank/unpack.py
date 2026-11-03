"""Reconstruct SHA-256-pinned S4 Lean sources for local/CI verification."""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import sys
import tempfile

SOURCE = Path(__file__).resolve().parent
DESTINATION = Path(sys.argv[1]).resolve()
FILES = {
    "S4Rank.lean": "94377c5747e235d82c2539ac5793336774170692461ccf7389222b7d38061dc8",
    "S4RankSource.lean": "a18b870a885b1914781ee920cf6d5453bc9a20cced08ebf934eb1fc3e58829f3",
}

lock_path = DESTINATION / ".agent34-s4rank.lock"
fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
try:
    for filename, digest in FILES.items():
        compressed = (SOURCE / (filename + ".xz.b64")).read_bytes()
        decoded = lzma.decompress(base64.b64decode(compressed))
        actual = hashlib.sha256(decoded).hexdigest()
        if actual != digest:
            raise ValueError(f"{filename}: SHA256 expected {digest}, got {actual}")
        tmp_fd, tmp_path = tempfile.mkstemp(prefix="." + filename + ".", dir=DESTINATION)
        try:
            with os.fdopen(tmp_fd, "wb") as output:
                output.write(decoded)
                output.flush()
                os.fsync(output.fileno())
            os.replace(tmp_path, DESTINATION / filename)
        finally:
            if os.path.exists(tmp_path):
                os.unlink(tmp_path)
        print(f"Verified and reconstructed {filename}: {digest}")
finally:
    os.close(fd)
    os.unlink(lock_path)
