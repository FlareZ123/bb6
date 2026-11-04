"""Restore the individually verified Lean/graph sources using atomic locked writes."""
from __future__ import annotations
import base64
import hashlib
import io
import os
import tarfile
from pathlib import Path
from filelock import FileLock

HERE = Path(__file__).resolve().parent
BUNDLE = HERE / "sources.tar.xz.b64"
EXPECTED = "4605e381d99e74556c3b9b563ae8b7b5c5e49b1a84384e52421f42f131f63717"
NAMES = {
    "Quotient.lean", "Quotient192.lean", "Bits8.lean",
    "Orbit8.lean", "make_bits.py", "rev_components.py",
}

def main() -> None:
    raw = base64.b64decode(BUNDLE.read_text(encoding="ascii").strip(), validate=True)
    actual = hashlib.sha256(raw).hexdigest()
    if actual != EXPECTED:
        raise ValueError(f"Bundle SHA256 mismatch: {actual}")
    with FileLock(str(HERE / ".sources.lock")):
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:xz") as archive:
            members = archive.getmembers()
            if {m.name for m in members} != NAMES or any(not m.isfile() for m in members):
                raise ValueError("Unexpected archive members")
            for member in members:
                data = archive.extractfile(member).read()
                destination = HERE / member.name
                temporary = HERE / (member.name + ".tmp")
                temporary.write_bytes(data)
                os.replace(temporary, destination)
                print(f"Restored {member.name}: {len(data)} bytes")
    print(f"SHA256 verified: {actual}")

if __name__ == "__main__":
    main()
