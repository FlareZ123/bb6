"""Reconstruct hash-pinned Lean proof sources from the repository archive."""
import base64
import fcntl
import hashlib
import io
import lzma
import os
from pathlib import Path
import tarfile
import tempfile

DIRECTORY = Path(__file__).resolve().parent
ARCHIVE_SHA256 = "84a19b58221f3a8afa04bf0cb226904f4a6d64c5ba0b67c275720d1240c98b6b"
SOURCES = {
    "Agent34CInverse.lean": "31086a2618a6674a018947fe63b3f1194232db15440b5804aaed1fe14cfaa9d1",
    "CReset184.lean": "8525710bcd08741dcc67c1e7e403a2432d0e4c9b3a3aaf254cb0f2e5fcb176ef",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    encoded = (DIRECTORY / "agent34-c184.tar.xz.b64").read_bytes()
    archive = base64.b64decode(encoded, validate=False)
    assert sha256(archive) == ARCHIVE_SHA256
    with tarfile.open(fileobj=io.BytesIO(lzma.decompress(archive))) as tar:
        entries = {name: tar.extractfile(name).read() for name in SOURCES}
    for name, digest in SOURCES.items():
        assert sha256(entries[name]) == digest
    with (DIRECTORY / ".reconstruct.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for name, data in entries.items():
            descriptor, tempname = tempfile.mkstemp(dir=DIRECTORY, prefix=f".{name}.")
            try:
                with os.fdopen(descriptor, "wb") as output:
                    output.write(data)
                    output.flush()
                    os.fsync(output.fileno())
                os.replace(tempname, DIRECTORY / name)
            finally:
                if os.path.exists(tempname):
                    os.unlink(tempname)
    print("Reconstructed and SHA-256-verified:", ", ".join(SOURCES))


if __name__ == "__main__":
    main()
