"""Restore exact checkable sources from stored base64-gzip payloads.

Requires the filelock package. Each destination is SHA-256 checked and written
atomically under its own lock; running twice is safe.
"""
import base64
import gzip
import hashlib
import os
from pathlib import Path
import tempfile

from filelock import FileLock

HERE = Path(__file__).resolve().parent
FILES = {
    "ValuationReturn.lean": "c6eb9f6b9b7f5124a156b14c3fac299c97c38edd150fbcffe1f1a22e0a090d77",
    "burst_verify.py": "014a416ca576dfa87757bbb6aa407067daad557cdf92ac89daf433e8c2f84ad6",
}


def restore(name: str, sha256: str) -> None:
    target = HERE / name
    data = gzip.decompress(base64.b64decode((HERE / (name + ".gz.b64")).read_text(encoding="ascii")))
    actual = hashlib.sha256(data).hexdigest()
    if actual != sha256:
        raise ValueError(f"{name}: SHA-256 mismatch: {actual}")
    with FileLock(str(target) + ".lock"):
        if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest() == sha256:
            print(f"verified {name}: {sha256}")
            return
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode="wb", dir=HERE, delete=False) as f:
                temporary = Path(f.name)
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            os.replace(temporary, target)
            temporary = None
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    print(f"restored {name}: {sha256}")


if __name__ == "__main__":
    for name, sha256 in FILES.items():
        restore(name, sha256)
