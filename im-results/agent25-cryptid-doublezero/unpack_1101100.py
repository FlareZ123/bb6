"""Reconstruct the four source-connected Lean modules of the A/1101100 certificate.

The archive is verified before extracting named members; writes are atomic
and guarded by an inter-process lock.
"""
from pathlib import Path
import base64
import hashlib
import io
import os
import tarfile
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "A1101100Bundle.tar.xz.b64"
EXPECTED_SHA256 = "2747df87e59d4b2b9b33a075b0dddddb433595d359813172ce4710f1162c407f"
FILES = (
    "A1101100.lean",
    "A1101100TraceDef.lean",
    "A1101100TraceStep2.lean",
    "A1101100TraceNoPhysical.lean",
)


def main() -> None:
    with FileLock(str(ROOT / ".unpack1101100.lock")):
        data = base64.b64decode(ARCHIVE.read_bytes(), validate=True)
        digest = hashlib.sha256(data).hexdigest()
        if digest != EXPECTED_SHA256:
            raise ValueError(f"Archive SHA-256 mismatch: {digest}")
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as tar:
            if set(tar.getnames()) != set(FILES):
                raise ValueError("Unexpected bundle members")
            for name in FILES:
                info = tar.getmember(name)
                if not info.isfile():
                    raise ValueError(f"Member is not a regular file: {name}")
                source = tar.extractfile(info).read()
                dest = ROOT / name
                temp = ROOT / f".{name}.tmp"
                temp.write_bytes(source)
                os.replace(temp, dest)
                print(f"{name}: {hashlib.sha256(source).hexdigest()}")


if __name__ == "__main__":
    main()
