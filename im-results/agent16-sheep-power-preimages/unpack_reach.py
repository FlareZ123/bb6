"""Verify and reconstruct the last two Lean proof modules after unpack.py."""
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
EXPECTED_COMPRESSED_SHA256 = "fa47c40b7e6bc1f9a1f18010d0aef97468879a43fe24eb55ead6a81b589bc1d4"
EXPECTED_TAR_SHA256 = "ea12b6b3676932c5fced1c6d0a6038601e569328d718ad1ab359388a3adbcc20"
EXPECTED_FILES = {
    "Special.lean": "9a26757c45cb03c049b47bccf76cbb5732275d2da2e3b12e5a2a33177462d485",
    "Reach.lean": "8160c9673de26f211deefe2702781548ced560574f23e0b5bb3963c98b0b6337",
}


def verify(data: bytes, expected: str) -> None:
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"SHA256 does not match expected digest {expected}")


def main() -> None:
    with FileLock(str(ROOT / ".unpack.lock")):
        packed = base64.b64decode((ROOT / "formal-reach.tar.xz.b64").read_bytes())
        verify(packed, EXPECTED_COMPRESSED_SHA256)
        raw = lzma.decompress(packed)
        verify(raw, EXPECTED_TAR_SHA256)
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as tar:
            members = tar.getmembers()
            assert len(members) == len(EXPECTED_FILES)
            assert set(m.name for m in members) == set(EXPECTED_FILES)
            for member in members:
                assert member.isfile()
                source = tar.extractfile(member)
                assert source is not None
                data = source.read()
                verify(data, EXPECTED_FILES[member.name])
                fd, tmp = tempfile.mkstemp(dir=ROOT, prefix=".proof-", suffix=".tmp")
                try:
                    with os.fdopen(fd, "wb") as output:
                        output.write(data)
                        output.flush()
                        os.fsync(output.fileno())
                    os.replace(tmp, ROOT / member.name)
                finally:
                    if os.path.exists(tmp):
                        os.unlink(tmp)
                print("Verified and restored:", member.name)


if __name__ == "__main__":
    main()
