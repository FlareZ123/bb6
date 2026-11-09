"""Restore checksum-verified standalone fifth-level Lean proof sources.

Restore fourth-level sources first: they supply the reusable power-period lemma.
All writes are atomic and serialized with a cross-platform process lock.
"""
import base64
import hashlib
import io
import lzma
import os
from pathlib import Path
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent
ARCHIVE_SHA256 = "887406ce6765cf7fee9b11a56b5f21d5a99af9e5ad7195095cbcf2fd2a7856ff"
MANIFEST = {
    "PowerGateH5.lean": "05fc26d424a5665bdffeebc4b024d0d9dd50189edca1c907be9dfdef4a2dff1a",
    "PowerGateH5Decision.lean": "ea47ea1704892ffa08b383c50ad63b1b04ebbded10f056e6c44df0bc59c7f32c",
    "verify_h5.py": "5784c13aed17f5f595f425ef90a7b513480285ac0fa8b5713b3ffdcff696e2db",
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    blob = base64.b64decode((ROOT / "h5-proof.tar.xz.b64").read_text().strip(), validate=True)
    assert digest(blob) == ARCHIVE_SHA256, "Proof archive checksum mismatch"
    with tarfile.open(fileobj=io.BytesIO(lzma.decompress(blob)), mode="r:") as archive:
        assert set(archive.getnames()) == set(MANIFEST)
        sources = {}
        for filename, checksum in MANIFEST.items():
            info = archive.getmember(filename)
            assert info.isfile()
            entry = archive.extractfile(info)
            assert entry is not None
            data = entry.read()
            assert digest(data) == checksum, "Corrupted source: " + filename
            sources[filename] = data

    with (ROOT / ".restore.lock").open("a+b") as lock:
        if os.name == "nt":
            import msvcrt
            lock.seek(0, os.SEEK_END)
            if lock.tell() == 0:
                lock.write(b"0")
                lock.flush()
            lock.seek(0)
            msvcrt.locking(lock.fileno(), msvcrt.LK_LOCK, 1)
        else:
            import fcntl
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        try:
            for filename, data in sources.items():
                with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
                    temporary = tmp.name
                    tmp.write(data)
                    tmp.flush()
                    os.fsync(tmp.fileno())
                os.replace(temporary, ROOT / filename)
                print("restored", filename, digest(data))
        finally:
            if os.name == "nt":
                msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


if __name__ == "__main__":
    main()
