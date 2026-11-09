"""Restore the source-checked, hash-locked standalone Lean cancellation sieve."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ENCODED = ROOT / "CancellationMod7Joint.lean.xz.b64"
OUTPUT = ROOT / "CancellationMod7Joint.lean"
EXPECTED_SHA256 = "ac8f3b0b01d6301bed6d4bbd3e87a706ccd8cc1b30ff7bbf237a3134d694ec02"


def main() -> None:
    source = lzma.decompress(base64.b64decode(ENCODED.read_text(encoding="ascii")))
    actual = hashlib.sha256(source).hexdigest()
    if actual != EXPECTED_SHA256:
        raise ValueError(f"Source SHA-256 mismatch: {actual}")

    with FileLock(str(OUTPUT) + ".lock"):
        if OUTPUT.exists() and OUTPUT.read_bytes() == source:
            print(f"Already verified: {OUTPUT} ({actual})")
            return
        with tempfile.NamedTemporaryFile(mode="wb", dir=ROOT, prefix=".mod7-", delete=False) as stream:
            temp_path = Path(stream.name)
            stream.write(source)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            os.replace(temp_path, OUTPUT)
        finally:
            temp_path.unlink(missing_ok=True)
    print(f"Restored: {OUTPUT} ({actual})")


if __name__ == "__main__":
    main()
