"""Reconstruct all Lean sources, checking hashes and using atomic locked replacement."""
from __future__ import annotations

import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "BB6Coverage": "fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd",
    "SparseCoverage": "c2271613c1c9676e1ef1cd92ed0ad07647e1e0187a11614a5d9e643c01cbc809",
    "LassoCoverage": "8544a335fb62a34329dc0c07edeeb5a948a3afb7a314b95f7d1f712cfb57c730",
    "ShiftCoverage": "3ea7b0bbac9b2ca575b34c362b478e52c335d390113b2934a4c73b0e2f309c3e",
    "StateClosed": "666d29e4b53a112800a7dd77807dab1dea7e2dc0cd8fd2b34b1b85bf353cd53f",
    "InvariantCoverage": "d2035331571ad04569b5dd457e3cd088b0c72864f0deaf521e21cce90bef8f28",
    "TreeCoverage": "5042442a7ce04c278bbbb1fda825d884be5b63eb96913d66d446bc9b27a5daa3",
    "FiniteTapeCoverage": "7ce8ab8c411038a0ca0f9ff568c23529dae4b7c514689dd2b14eb9c44bd17000",
    "FiniteTapeShift": "23bed37b7c46bc7d46714700605ca9309656a99558a8565b2b15c877fd194579",
    "FiniteLeafChecks": "2a11ad35af233d1107cde5e7dd7f7c12f0ec3c1ad641e278d073ba4bd46a23db",
    "LeafDemo": "20903fb75208dd55226de5cfacea38a15911a97b2522d827172f32c15ba06983",
}


def reconstruct(name: str, expected: str) -> None:
    source = ROOT / f"{name}.lean.xz.b64"
    target = ROOT / f"{name}.lean"
    payload = lzma.decompress(base64.b64decode(source.read_text().strip()))
    digest = hashlib.sha256(payload).hexdigest()
    if digest != expected:
        raise ValueError(f"{name}: source checksum mismatch: {digest}")
    lock = ROOT / f"{name}.lean.lock"
    descriptor = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    temporary = None
    try:
        if target.exists() and target.read_bytes() == payload:
            print(f"Verified existing {name}.lean: {digest}")
            return
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix=f"{name}.", suffix=".tmp", delete=False) as out:
            temporary = Path(out.name)
            out.write(payload)
            out.flush()
            os.fsync(out.fileno())
        os.replace(temporary, target)
        temporary = None
        print(f"Verified and wrote {name}.lean: {digest}")
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
        os.close(descriptor)
        lock.unlink()


def main() -> None:
    for name, expected in SOURCES.items():
        reconstruct(name, expected)


if __name__ == "__main__":
    main()
