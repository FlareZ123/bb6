"""Restore the seven byte-exact exceptional-branch sources atomically.

Verifies the complete archive and an exact filename allowlist before extraction.
"""
from __future__ import annotations

import base64
import hashlib
import io
import os
from pathlib import Path
import tarfile
import tempfile

from filelock import FileLock

HERE = Path(__file__).resolve().parent
SHA256 = "347f8112cca9b4456e6269c82fe3919d622ea7897f9f6f7e44fd1db164d53adc"
FILES = (
    "DExceptional.lean",
    "DWordGrammar.lean",
    "DABranch.lean",
    "primitive.py",
    "test_two_return.py",
    "test_A_rejoin.py",
    "test_rejoin.py",
)


def restore() -> None:
    data = base64.b64decode(
        (HERE / "ExceptionalSources.tar.xz.b64").read_text(encoding="ascii").strip(),
        validate=True,
    )
    digest = hashlib.sha256(data).hexdigest()
    if digest != SHA256:
        raise ValueError(f"Archive SHA256 mismatch: {digest}")
    with FileLock(str(HERE / ".restore.lock")):
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as archive:
            expected = sorted(FILES)
            found = sorted(
                m.name.removeprefix("./") for m in archive.getmembers() if m.isfile()
            )
            if found != expected:
                raise ValueError(f"Unexpected archive file list: {found}")
            for name in FILES:
                source = archive.extractfile("./" + name)
                if source is None:
                    raise ValueError(f"Missing member: {name}")
                payload = source.read()
                tmp_name = None
                try:
                    with tempfile.NamedTemporaryFile(
                        mode="wb", dir=HERE, prefix=f".{name}.", delete=False
                    ) as output:
                        tmp_name = output.name
                        output.write(payload)
                        output.flush()
                        os.fsync(output.fileno())
                    os.replace(tmp_name, HERE / name)
                finally:
                    if tmp_name is not None and os.path.exists(tmp_name):
                        os.unlink(tmp_name)
                print(f"Restored {name} ({len(payload)} bytes)")


if __name__ == "__main__":
    restore()
