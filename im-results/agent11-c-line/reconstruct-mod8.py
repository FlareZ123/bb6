"""Reconstruct the formally checked mod-8 gate certificates.

Requires the filelock package, verifies archive and per-file SHA-256,
and performs atomic replacement while holding a directory lock.
"""
from __future__ import annotations
import base64
import hashlib
import io
import lzma
import os
from pathlib import Path
import tarfile
import tempfile
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
B64_HASH = "79ce55ed68831d68355f2b818deb6a969dc67b8063bc50563fbedb3be739e618"
TAR_HASH = "a128a34fefdd12a9ecd3f10faa0053b64480a5b64de6181d634cf54b009f9c9d"
SOURCES = {
    "MoreResidue.lean": "dc6fe87cbf6c3b185997c5b5d7369e9c8a89bcf19729fbcf1f1ad876bfd7d475",
    "FinalGate.lean": "515d7e918642c93f16d70fc6e88cd9db626923b906eac6b7c83461331113d2a2",
}


def restore() -> None:
    with FileLock(str(ROOT / ".mod8-source.lock")):
        encoded = (ROOT / "mod8-lean.tar.xz.b64").read_text(encoding="ascii").strip()
        assert hashlib.sha256(encoded.encode("ascii")).hexdigest() == B64_HASH
        raw = lzma.decompress(base64.b64decode(encoded, validate=True))
        assert hashlib.sha256(raw).hexdigest() == TAR_HASH
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
            assert {i.name for i in archive.getmembers()} == set(SOURCES)
            for name, digest in SOURCES.items():
                member = archive.getmember(name)
                assert member.isfile()
                src = archive.extractfile(member)
                assert src is not None
                data = src.read()
                assert hashlib.sha256(data).hexdigest() == digest
                with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as temp:
                    temp.write(data)
                    temp.flush()
                    os.fsync(temp.fileno())
                    temporary = Path(temp.name)
                os.replace(temporary, ROOT / name)
                print(f"Restored {name}, SHA-256 verified")


if __name__ == "__main__":
    restore()
