"""Reconstruct pinned Lean source using an exclusive lock and atomic replacement."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "BSamplingLimits": "190f39e449d2fa48427e1ba7063cd258bd44b923f639f10b9b325c04792c4423",
    "BSamplingBound": "1633d7e3454b4146c87af2d887ad2a49dc9a65b23466138439bab8fc84c84cea",
}


def reconstruct(NAME: str, EXPECTED: str) -> None:
    payload = lzma.decompress(base64.b64decode((ROOT / f"{NAME}.lean.xz.b64").read_text().strip()))
    digest = hashlib.sha256(payload).hexdigest()
    if digest != EXPECTED:
        raise ValueError(f"source checksum mismatch: {digest}")
    target = ROOT / f"{NAME}.lean"
    lock = ROOT / f"{NAME}.lean.lock"
    fd = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    temporary = None
    try:
        if target.exists() and target.read_bytes() == payload:
            print(f"Verified {target.name}: {digest}")
            return
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix=f"{NAME}.", suffix=".tmp", delete=False) as out:
            temporary = Path(out.name)
            out.write(payload)
            out.flush()
            os.fsync(out.fileno())
        os.replace(temporary, target)
        temporary = None
        print(f"Verified and wrote {target.name}: {digest}")
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
        os.close(fd)
        lock.unlink()


def main() -> None:
    for name, expected in SOURCES.items():
        reconstruct(name, expected)


if __name__ == "__main__":
    main()
