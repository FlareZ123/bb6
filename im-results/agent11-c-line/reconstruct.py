"""Reconstruct the exact Lean gateway proofs from an xz/base64 bundle.

Requires Python's standard library plus the filelock package.
Writes are serialized and atomically replaced.
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
EXPECTED = {
    "LowGate.lean": "a3191b43d4e30d52846d1fd8005a02cd94f0862fa1d95e2bfa38e8c156037c0c",
    "BackGate.lean": "d1ccc18bc6f5a3b65d7163911a22ea68b7453b01e28465e92dc6f8bdc45d8aa5",
    "ResetGate.lean": "9844a48cd3868bcc3eda84fa80ab049917ad7989282df9492f55cc22fc09cf42",
}


def reconstruct() -> None:
    with FileLock(str(ROOT / ".reconstruct.lock")):
        encoded = (ROOT / "gates-lean.tar.xz.b64").read_text(encoding="ascii").strip()
        assert hashlib.sha256(encoded.encode("ascii")).hexdigest() == (
            "98a564526d624202b61bd37af38d231aa13fb563e7edae9453a8cfe7f8dba0dd"
        )
        raw = lzma.decompress(base64.b64decode(encoded, validate=True))
        assert hashlib.sha256(raw).hexdigest() == (
            "8beac4d083a533ae8f1be5c2211de61bf771126ef2abf302580e08c74633ab24"
        )
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
            members = archive.getmembers()
            assert {m.name for m in members} == set(EXPECTED)
            for name in EXPECTED:
                member = archive.getmember(name)
                assert member.isfile()
                extracted = archive.extractfile(member)
                assert extracted is not None
                data = extracted.read()
                assert hashlib.sha256(data).hexdigest() == EXPECTED[name]
                with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as temporary:
                    temporary.write(data)
                    temporary.flush()
                    os.fsync(temporary.fileno())
                    temp_name = temporary.name
                os.replace(temp_name, ROOT / name)
                print(f"Verified {name} ({len(data)} bytes)")


if __name__ == "__main__":
    reconstruct()
