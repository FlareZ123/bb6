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

SIDE_GENERATOR_SHA256 = "25366c7bdfa89a53bf6c354a937e818c500202c669b47fa7e1f0e59251776ef3"
with (HERE / ".reconstruct-side-generator.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raw = lzma.decompress(base64.b64decode((HERE / "generate_c_side_inverse.py.xz.b64").read_bytes()))
    actual = hashlib.sha256(raw).hexdigest()
    if actual != SIDE_GENERATOR_SHA256:
        raise ValueError(f"Side proof generator checksum mismatch: {actual}")
    fd, filename = tempfile.mkstemp(prefix=".sidegenerator.", suffix=".tmp", dir=HERE)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        os.replace(filename, HERE / "generate_c_side_inverse.py")
    finally:
        if os.path.exists(filename):
            os.unlink(filename)
print(f"Verified generate_c_side_inverse.py: {len(raw)} bytes, sha256={actual}")

SIDE_V2_SHA256 = "c10149c96c657683367db89671c2cad4728f5659bbda2473f4cf89696a5b9553"
with (HERE / ".reconstruct-side-generator-v2.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raw = lzma.decompress(base64.b64decode((HERE / "generate_c_side_inverse_v2.py.xz.b64").read_bytes()))
    actual = hashlib.sha256(raw).hexdigest()
    if actual != SIDE_V2_SHA256:
        raise ValueError(f"Affine proof generator checksum mismatch: {actual}")
    fd, filename = tempfile.mkstemp(prefix=".sidegenv2.", suffix=".tmp", dir=HERE)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        os.replace(filename, HERE / "generate_c_side_inverse_v2.py")
    finally:
        if os.path.exists(filename):
            os.unlink(filename)
print(f"Verified generate_c_side_inverse_v2.py: {len(raw)} bytes, sha256={actual}")

RESET_V2_SHA256 = "ed307881016cd207b4de2859f1c964e9311112851aceafd9bf59972395d2be3d"
with (HERE / ".reconstruct-reset-generator-v2.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    raw = lzma.decompress(base64.b64decode((HERE / "generate_c_inverse_v2.py.xz.b64").read_bytes()))
    actual = hashlib.sha256(raw).hexdigest()
    if actual != RESET_V2_SHA256:
        raise ValueError(f"Affine reset generator checksum mismatch: {actual}")
    fd, filename = tempfile.mkstemp(prefix=".resetgenv2.", suffix=".tmp", dir=HERE)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        os.replace(filename, HERE / "generate_c_inverse_v2.py")
    finally:
        if os.path.exists(filename):
            os.unlink(filename)
print(f"Verified generate_c_inverse_v2.py: {len(raw)} bytes, sha256={actual}")
