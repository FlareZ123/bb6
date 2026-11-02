"""Decode the Agent 29 four-residue Lean proof after SHA-256 verification.

The byte-identical source was generated from complete symbolic predecessor trees.
This script performs only a data reconstruction; Lean audits every theorem.
"""
from pathlib import Path
import base64
import fcntl
import hashlib
import lzma
import os
import tempfile

HERE = Path(__file__).resolve().parent
EXPECTED = "d615840ed77b8915adc9eceee042e144fa6a5be62dfc554f971ba95d59368e16"
with (HERE / ".reconstruct.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raw = lzma.decompress(base64.b64decode((HERE / "CNew.lean.xz.b64").read_bytes()))
    actual = hashlib.sha256(raw).hexdigest()
    if actual != EXPECTED:
        raise ValueError(f"CNew checksum mismatch: {actual}")
    fd, filename = tempfile.mkstemp(prefix=".CNew.", suffix=".tmp", dir=HERE)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        os.replace(filename, HERE / "CNew.lean")
    finally:
        if os.path.exists(filename):
            os.unlink(filename)
print(f"Verified CNew.lean: {len(raw)} bytes, sha256={actual}")

GENERATOR_SHA256 = "404009872f56a9b5b08f7994a1ab45b810b6cedcd9823d3ed16aa8a0d09c0bf4"
with (HERE / ".reconstruct-generator.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raw = lzma.decompress(base64.b64decode((HERE / "generate_c_inverse.py.xz.b64").read_bytes()))
    actual = hashlib.sha256(raw).hexdigest()
    if actual != GENERATOR_SHA256:
        raise ValueError(f"Proof generator checksum mismatch: {actual}")
    fd, filename = tempfile.mkstemp(prefix=".generator.", suffix=".tmp", dir=HERE)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        os.replace(filename, HERE / "generate_c_inverse.py")
    finally:
        if os.path.exists(filename):
            os.unlink(filename)
print(f"Verified generate_c_inverse.py: {len(raw)} bytes, sha256={actual}")
