"""Restore the complete Lean physical-window refinement source, verifying its digest.

The large proof is stored losslessly as xz+base64. This script uses a lock
and atomic replacement to keep the generated Lean module coherent in CI.
"""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
import sys
import tempfile
from pathlib import Path

from filelock import FileLock

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "PhysicalWindow.lean.xz.b64"
EXPECTED_SHA256 = "bb9d2a00af05385f1c07ba10dc6cd7adbab3e37128c542d4db582b3aa463fca9"


def restore(output: Path) -> None:
    encoded = SOURCE.read_text(encoding="ascii").strip()
    data = lzma.decompress(base64.b64decode(encoded, validate=True))
    digest = hashlib.sha256(data).hexdigest()
    if digest != EXPECTED_SHA256:
        raise ValueError(f"PhysicalWindow source checksum mismatch: {digest}")
    output.parent.mkdir(parents=True, exist_ok=True)
    with FileLock(str(output) + ".lock"):
        with tempfile.NamedTemporaryFile(
            mode="wb", dir=output.parent, prefix=".physical-window-",
            delete=False,
        ) as tmp:
            tmp.write(data)
            tmp.flush()
            os.fsync(tmp.fileno())
            temp_name = tmp.name
        os.replace(temp_name, output)
    print(f"Restored {output}: {len(data)} bytes, sha256={digest}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python restore_physical.py OUTPUT_DIRECTORY")
    restore(Path(sys.argv[1]) / "PhysicalWindow.lean")
