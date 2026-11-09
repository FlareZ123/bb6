"""Restore the exact Lean 4.36.0-rc2 source and independent checker.

The archive is content-addressed, names are restricted to a fixed manifest,
and writes are atomic under a cross-platform process lock.
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
ARCHIVE_SHA256 = "beab91d9692214394ddeda0fc6bd1e9cef50d8c9593aeb7186c8c645527a0cdf"
MANIFEST = {
    "ResidueGap.lean": "a7ed6e2114af322a1cbfc85ac3e1e743a74762c78ef038a325ca32d1ddb54147",
    "PowerGateH4.lean": "ded1902b1c2daff92f5a4343e75306d8cfdb2cb0960287aa2e712e4e854773f8",
    "PowerGateH4Decision.lean": "9cdae7be0727c2cfe91d4013f30e0e6a1f1d31bb3dbc3aa47ba85a06ce45c9ea",
    "verify_h4.py": "85131a468a4900c7774a91889e3f26184ce10cbc2f0ca214f895ca341b3504da",
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    archive = base64.b64decode((ROOT / "h4-proof.tar.xz.b64").read_text().strip(), validate=True)
    assert digest(archive) == ARCHIVE_SHA256, "Compressed proof archive has changed"
    uncompressed = lzma.decompress(archive)
    with tarfile.open(fileobj=io.BytesIO(uncompressed), mode="r:") as tar:
        assert set(tar.getnames()) == set(MANIFEST), "Unexpected archive members"
        source = {}
        for name, expected in MANIFEST.items():
            member = tar.getmember(name)
            assert member.isfile(), "Archive contains a non-file member"
            entry = tar.extractfile(member)
            assert entry is not None
            data = entry.read()
            assert digest(data) == expected, "Source checksum mismatch: " + name
            source[name] = data

    lock_path = ROOT / ".restore.lock"
    with lock_path.open("a+b") as lock:
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
            for name, data in source.items():
                with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
                    tmp_name = tmp.name
                    tmp.write(data)
                    tmp.flush()
                    os.fsync(tmp.fileno())
                os.replace(tmp_name, ROOT / name)
                print("restored", name, digest(data))
        finally:
            if os.name == "nt":
                msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


if __name__ == "__main__":
    main()
