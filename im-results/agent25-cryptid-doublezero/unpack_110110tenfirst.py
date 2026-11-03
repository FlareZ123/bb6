"""Verify and atomically reconstruct the all-q 110110(10)^q0 source certificate."""
from pathlib import Path
import base64
import hashlib
import lzma
import os
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
EXPECTED = "35a2bdf90b7831a3a222f8c877ed6443318d95bf32998a944f822982255dc516"


def main() -> None:
    with FileLock(str(ROOT / ".unpack110110tenfirst.lock")):
        data = base64.b64decode(
            (ROOT / "A110110TenFirst.lean.xz.b64").read_bytes().strip(),
            validate=True,
        )
        source = lzma.decompress(data)
        digest = hashlib.sha256(source).hexdigest()
        if digest != EXPECTED:
            raise ValueError(f"SHA-256 mismatch: {digest}")
        dest = ROOT / "A110110TenFirst.lean"
        tmp = ROOT / ".A110110TenFirst.lean.tmp"
        tmp.write_bytes(source)
        os.replace(tmp, dest)
        print(f"Decoded {dest.name}: {digest}")


if __name__ == "__main__":
    main()
