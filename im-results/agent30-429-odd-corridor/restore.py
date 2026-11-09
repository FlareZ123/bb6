"""Restore verified Lean source files using atomic, locked writes."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "BB429OddEvenCorridor": "524d8046bea7a051f406aed4192af8f89b087904f74ba2b3d1b6b3b53b530061",
    "BB429OddEvenCorridorMax": "59d8fa26979247b7e37dd91054eacd3d2c4242c88ed57a55bd236967674ee5e5",
    "BB429OddEvenCorridorCount": "5b52cb2e03f037c33a3a233ea431e6d1129f692a949b578dbcc923b65b404a95",
}


def restore() -> None:
    for name, digest in EXPECTED.items():
        source = ROOT / f"{name}.lean.xz.b64"
        target = ROOT / f"{name}.lean"
        decoded = lzma.decompress(base64.b64decode(source.read_text(encoding="ascii")))
        actual = hashlib.sha256(decoded).hexdigest()
        if actual != digest:
            raise ValueError(f"SHA-256 mismatch in {source}: {actual}")
        lock_path = ROOT / f".{name}.restore.lock"
        with lock_path.open("a+b") as lock:
            if os.name == "nt":
                import msvcrt

                lock.seek(0)
                msvcrt.locking(lock.fileno(), msvcrt.LK_LOCK, 1)
            else:
                import fcntl

                fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
            try:
                if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest() == digest:
                    continue
                fd, temporary = tempfile.mkstemp(dir=ROOT, prefix=f".{name}.", suffix=".tmp")
                try:
                    with os.fdopen(fd, "wb") as output:
                        output.write(decoded)
                        output.flush()
                        os.fsync(output.fileno())
                    os.replace(temporary, target)
                finally:
                    if os.path.exists(temporary):
                        os.unlink(temporary)
            finally:
                if os.name == "nt":
                    lock.seek(0)
                    msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
                else:
                    fcntl.flock(lock.fileno(), fcntl.LOCK_UN)
        print(f"Restored {name}.lean, SHA-256 {digest}")


if __name__ == "__main__":
    restore()
