"""Restore the mod-13 joint cancellation sieve with verified bytes and atomic writes."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "CancellationMod13Joint.lean.xz.b64"
OUTPUT = ROOT / "CancellationMod13Joint.lean"
EXPECTED = "fc7bd12031bf075027d3449257692aaf2bd00ed43acbb29a3905de9000bbce03"


def main() -> None:
    source = lzma.decompress(base64.b64decode(SOURCE.read_text(encoding="ascii")))
    actual = hashlib.sha256(source).hexdigest()
    if actual != EXPECTED:
        raise ValueError(f"SHA256 mismatch: {actual}")
    with FileLock(str(OUTPUT) + ".lock"):
        if OUTPUT.exists() and OUTPUT.read_bytes() == source:
            print(f"Verified: {OUTPUT}, SHA256={actual}")
            return
        with tempfile.NamedTemporaryFile(mode="wb", dir=ROOT, prefix=".mod13-", delete=False) as stream:
            temp = Path(stream.name)
            stream.write(source)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.replace(temp, OUTPUT)
        finally:
            temp.unlink(missing_ok=True)
    print(f"Restored: {OUTPUT}, SHA256={actual}")


if __name__ == "__main__":
    main()
