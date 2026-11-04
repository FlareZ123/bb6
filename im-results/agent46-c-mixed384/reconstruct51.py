"""Reconstruct the exact Agent46 C51 Lean proof with SHA verification, atomically."""
import base64
import fcntl
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "C51.lean.xz.b64"
DESTINATION = ROOT / "C51.lean"
EXPECTED_SHA256 = "77dfc0a2cf8d8d86bbb75385ef1062f1d98a13cc8049f2420f7d3ba6685fe809"


def reconstruct() -> None:
    with (ROOT / ".reconstruct51.lock").open("w", encoding="utf-8") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        source = lzma.decompress(base64.b64decode(ARCHIVE.read_text(encoding="ascii")))
        digest = hashlib.sha256(source).hexdigest()
        if digest != EXPECTED_SHA256:
            raise ValueError(f"C51 proof SHA256 mismatch: {digest}")
        with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as output:
            output.write(source)
            temp_name = output.name
        os.replace(temp_name, DESTINATION)
        print(f"C51 Lean original source: {len(source)} bytes, SHA256 {digest}")


if __name__ == "__main__":
    reconstruct()
