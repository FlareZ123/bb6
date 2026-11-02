"""Reconstruct the Lean source with a source hash check and atomic locked replacement."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "BB6Coverage.lean.xz.b64"
TARGET = ROOT / "BB6Coverage.lean"
EXPECTED = "fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd"


def main() -> None:
    payload = lzma.decompress(base64.b64decode(SOURCE.read_text().strip()))
    digest = hashlib.sha256(payload).hexdigest()
    if digest != EXPECTED:
        raise ValueError(f"Source checksum mismatch: {digest}")
    lock = TARGET.with_suffix(".lean.lock")
    descriptor = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    temporary = None
    try:
        if TARGET.exists() and TARGET.read_bytes() == payload:
            print(f"Verified existing {TARGET.name}: {digest}")
            return
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix="BB6Coverage.", suffix=".tmp", delete=False) as out:
            temporary = Path(out.name)
            out.write(payload)
            out.flush()
            os.fsync(out.fileno())
        os.replace(temporary, TARGET)
        temporary = None
        print(f"Verified and wrote {TARGET.name}: {digest}")
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
        os.close(descriptor)
        lock.unlink()


if __name__ == "__main__":
    main()
