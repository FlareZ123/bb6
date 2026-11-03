"""Verify and restore original-machine A-row formal proof sources (Agent 2)."""
from __future__ import annotations
import base64
import hashlib
import io
import os
from pathlib import Path
import tarfile
from tempfile import NamedTemporaryFile
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "ARegularSourceBundle.tar.xz.b64"
EXPECTED = "8e0f2ad4e3d0f53daa8bdd82234c632ba06c0563aff30e0f8e1e086a6ce12ccd"
MEMBERS = ("AWordAlgebra.lean", "ATwoSource.lean", "ARegularFull.lean")

with FileLock(str(ROOT / ".a-regular-bundle.lock")):
    payload = base64.b64decode(ARCHIVE.read_text(encoding="ascii").strip(), validate=True)
    if hashlib.sha256(payload).hexdigest() != EXPECTED:
        raise ValueError("A-source proof archive SHA256 mismatch")
    with tarfile.open(fileobj=io.BytesIO(payload), mode="r:xz") as archive:
        names = tuple(member.name for member in archive.getmembers())
        if names != MEMBERS:
            raise ValueError(f"Unexpected proof bundle members: {names}")
        for name in MEMBERS:
            data = archive.extractfile(name).read()
            with NamedTemporaryFile(dir=ROOT, prefix=".a-source-", delete=False) as tmp:
                tmp.write(data)
                tmp.flush()
                os.fsync(tmp.fileno())
                staged = Path(tmp.name)
            os.replace(staged, ROOT / name)
    print("Restored and SHA256-verified:", ", ".join(MEMBERS))
