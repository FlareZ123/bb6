#!/usr/bin/env python3
"""Reconstruct locally kernel-checked variant sources from pinned inputs."""
from pathlib import Path
import base64, hashlib, io, lzma, tarfile

HERE = Path(__file__).resolve().parent
old = HERE.parent / "agent31-cryptid-boundary" / "Boundary.lean.xz.b64"
source = lzma.decompress(base64.b64decode(old.read_bytes()))
assert hashlib.sha256(source).hexdigest() == "0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883"
assert source.count(b"| 4, true  => goL c false 1") == 1
source = source.replace(b"CryptidBoundary", b"D3SiblingBoundary")
source = source.replace(b"| 4, true  => goL c false 1", b"| 4, true  => goL c false 3")
(HERE / "D3SiblingBoundary.lean").write_bytes(source)
arc = base64.b64decode((HERE / "d3-sibling-proof.tar.xz.b64").read_bytes())
assert hashlib.sha256(arc).hexdigest() == "5f4d559bf90e33565fe361e937b5e22cdda0b2bbfe8a7a08f7d1ca692108b8b0"
with tarfile.open(fileobj=io.BytesIO(arc),mode="r:xz") as tf:
    for name in ("D3SiblingGuard.lean", "D3SiblingInvariant.lean"):
        f = tf.extractfile(name)
        assert f is not None
        (HERE / name).write_bytes(f.read())
