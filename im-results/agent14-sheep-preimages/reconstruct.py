"""Restore the Lean proof from the original certificate and its extension.

Requires Python 3 and the filelock package. Reconstructs deterministically,
checks both source SHA-256 hashes, and writes atomically under a file lock.
"""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import base64
import hashlib
import lzma
import os

ROOT = Path(__file__).resolve().parent
BASE_HASH = "db7231175872784f2e812d54aecbfad8559459da6d5a5090dfb521bee23f453c"
EXT_HASH = "26e1631f4aaad05d54d090068a9a0451d034915adcf728eb9948bef4afc242a4"
FINAL_HASH = "07a0e4367dd12e2f734257cc7bd4804488c161095e8434540f372399926e57c7"
MARKER = b"#print axioms SheepPreimages.no_large_v2_preimage"


def unpack(filename: str, expected: str) -> bytes:
    data = lzma.decompress(base64.b64decode((ROOT / filename).read_bytes().strip()))
    assert hashlib.sha256(data).hexdigest() == expected, filename
    return data


def main() -> None:
    base = unpack("Triple.lean.xz.b64", BASE_HASH)
    extension = unpack("Extension.xz.b64", EXT_HASH)
    assert base.count(MARKER) == 1
    source = base.split(MARKER, 1)[0] + extension
    assert hashlib.sha256(source).hexdigest() == FINAL_HASH

    target = ROOT / "Triple.lean"
    with FileLock(str(target) + ".lock"):
        if target.exists() and target.read_bytes() == source:
            print(f"Verified existing {target.name}: SHA256 {FINAL_HASH}")
            return
        with NamedTemporaryFile(dir=ROOT, prefix=".triple-", suffix=".tmp", delete=False) as tmp:
            tmp.write(source)
            tmp.flush()
            os.fsync(tmp.fileno())
            temporary = Path(tmp.name)
        os.replace(temporary, target)
    print(f"Restored {target.name}: {len(source)} bytes; SHA256 {FINAL_HASH}")


if __name__ == "__main__":
    main()
