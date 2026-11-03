"""Restore byte-exact E-ladder Lean theorem and independent raw checker."""
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
SHA256 = "09e5960b75a793a32a1579d5b4775546b0983e071b8f6201dab52fa79be0f423"
FILES = ("DETripleLadder.lean", "test_E_ladder.py")


def restore() -> None:
    data = base64.b64decode(
        (HERE / "ELadderSources.tar.xz.b64").read_text(encoding="ascii").strip(),
        validate=True,
    )
    digest = hashlib.sha256(data).hexdigest()
    if digest != SHA256:
        raise ValueError(f"Archive SHA256 mismatch: {digest}")
    with FileLock(str(HERE / ".restore.lock")):
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as archive:
            found = sorted(
                m.name.removeprefix("./") for m in archive.getmembers() if m.isfile()
            )
            if found != sorted(FILES):
                raise ValueError(f"Unexpected archive file list: {found}")
            for name in FILES:
                member = archive.extractfile("./" + name)
                if member is None:
                    raise ValueError(f"Missing member: {name}")
                payload = member.read()
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
