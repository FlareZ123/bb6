"""Decode and verify the self-contained Lean certificate with an atomic, locked write."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

EXPECTED_SHA256 = {
    "S4Prefix.lean": "6989f300afae69d21c8f79b931d9c2bbd3b85851ea1ec7951ad6eed2c96e298a",
    "S4Length.lean": "19c793633233f7f9b730b14ef95f2b3c33a6bd92899ef5b34b9a876af3b37436",
}


def reconstruct(folder: Path, name: str) -> Path:
    raw = lzma.decompress(base64.b64decode((folder / (name + ".xz.b64")).read_text().strip()))
    actual = hashlib.sha256(raw).hexdigest()
    if actual != EXPECTED_SHA256[name]:
        raise ValueError(f"Certificate digest mismatch: {actual}")

    target = folder / name
    with (folder / (name + ".lock")).open("a+b") as lock:
        if os.name == "nt":
            import msvcrt
            lock.seek(0)
            lock.write(b"\0")
            lock.flush()
            lock.seek(0)
            msvcrt.locking(lock.fileno(), msvcrt.LK_LOCK, 1)
        else:
            import fcntl
            fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            with tempfile.NamedTemporaryFile(dir=folder, prefix="." + name + ".", delete=False) as tmp:
                name = tmp.name
                tmp.write(raw)
                tmp.flush()
                os.fsync(tmp.fileno())
            os.replace(name, target)
        finally:
            if os.name == "nt":
                lock.seek(0)
                msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(lock, fcntl.LOCK_UN)
    return target


if __name__ == "__main__":
    for name in EXPECTED_SHA256:
        print(f"Wrote SHA256-checked {reconstruct(Path(__file__).resolve().parent, name)}")
