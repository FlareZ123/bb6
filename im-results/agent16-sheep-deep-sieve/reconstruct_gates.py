"""Atomically reconstruct kernel-verified Sheep finite modular certificates."""
from __future__ import annotations

import base64
import hashlib
import io
import lzma
import os
import tarfile
import tempfile
from pathlib import Path

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "finite-gates.tar.xz.b64"
COMPRESSED_SHA256 = "a25fa02158a0bc73c3a2aba452d6a18e395eacd8f68d524dcfb0d7fbc4305b41"
SOURCE_HASHES = {
    "FiniteModCert.lean": "903ea4250dccfb149ecbc0396e437f8c9863fb78b36cbfb313cdd115073dadbd",
    "FiniteGates0.lean": "c4d37e60158c03ece14ee06cdb9ebe895bf0d3c18ed2a96befdb728dfef1b706",
    "FiniteGates1.lean": "e4a7088234a750a671ce589894acfdfb55a3ec15f48e9c3fc3b93206c1745c68",
    "FiniteGates2.lean": "63ab1a54fb4c80f7e406ec373eccd84766837791de6ec37e8e1f71a30e1a6b72",
    "FiniteGates3.lean": "c8e0c55685e0b99333d85756ca51207f730ecfe853261ea5e6080ff38c8a4942",
    "FiniteGates4.lean": "bde2bd620481a9f98475e7cbc33256107c11f9d0622f472b36580842aa754105",
    "FiniteGates5.lean": "015f5e41704bf4e48ba15ed214ccbf440c0b7aff353ada0accc8fbf7c86d589c",
    "FiniteGates6.lean": "64be5567307e2017241991208917c76d9eb33b86c630dc8db7e43304330516d2",
    "FiniteGates7.lean": "51a8972dd10f4ec60b0cc6b7ec9cc5f1beaf41c87b272940fd22de70dbea52e8",
}


def assert_sha256(value: bytes, expected: str) -> None:
    actual = hashlib.sha256(value).hexdigest()
    if actual != expected:
        raise ValueError(f"SHA256 mismatch: {actual} != {expected}")


def reconstruct() -> tuple[Path, ...]:
    compressed = base64.b64decode(ARCHIVE.read_bytes())
    assert_sha256(compressed, COMPRESSED_SHA256)
    extracted = lzma.decompress(compressed)
    restored = []
    with tarfile.open(fileobj=io.BytesIO(extracted), mode="r:") as archive:
        if set(archive.getnames()) != set(SOURCE_HASHES):
            raise ValueError("Unexpected module list")
        for name, expected in SOURCE_HASHES.items():
            member = archive.getmember(name)
            if not member.isfile():
                raise ValueError(f"Not a regular Lean module: {name}")
            data_stream = archive.extractfile(member)
            assert data_stream is not None
            data = data_stream.read()
            assert_sha256(data, expected)
            path = ROOT / name
            with FileLock(str(path) + ".lock"):
                fd, temp = tempfile.mkstemp(prefix=f".{name}.", dir=ROOT)
                try:
                    with os.fdopen(fd, "wb") as stream:
                        stream.write(data)
                        stream.flush()
                        os.fsync(stream.fileno())
                    os.replace(temp, path)
                finally:
                    if os.path.exists(temp):
                        os.unlink(temp)
            restored.append(path)
    return tuple(restored)


if __name__ == "__main__":
    for file in reconstruct():
        print(f"Verified Lean source: {file.name}")
