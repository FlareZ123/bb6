"""Verify and restore the four byte-exact locally checked research sources.

Only the four whitelisted archive members are extracted. Output writes use an
exclusive lock, fsync, and atomic replacement to avoid partial source files.
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
EXPECTED_SHA256 = "33380f7460ac295ee259d6e81182cd57afdcbbabdf73b0d8a729e49c077cd18b"
EXPECTED_FILES = (
    "DRegular.lean",
    "DTransport.lean",
    "d_return_model.py",
    "check_raw.py",
)


def restore() -> None:
    raw = base64.b64decode(
        (HERE / "LeanSources.tar.xz.b64").read_text(encoding="ascii").strip(),
        validate=True,
    )
    actual = hashlib.sha256(raw).hexdigest()
    if actual != EXPECTED_SHA256:
        raise ValueError(f"Archive digest mismatch: {actual}")

    with FileLock(str(HERE / ".restore.lock")):
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:xz") as archive:
            actual_files = sorted(
                m.name.removeprefix("./")
                for m in archive.getmembers()
                if m.isfile()
            )
            if actual_files != sorted(EXPECTED_FILES):
                raise ValueError(f"Unexpected source manifest: {actual_files}")

            for name in EXPECTED_FILES:
                source = archive.extractfile("./" + name)
                if source is None:
                    raise ValueError(f"Missing source bytes: {name}")
                data = source.read()
                tmp_name = None
                try:
                    with tempfile.NamedTemporaryFile(
                        mode="wb", dir=HERE, prefix=f".{name}.", delete=False
                    ) as tmp:
                        tmp_name = tmp.name
                        tmp.write(data)
                        tmp.flush()
                        os.fsync(tmp.fileno())
                    os.replace(tmp_name, HERE / name)
                finally:
                    if tmp_name is not None and os.path.exists(tmp_name):
                        os.unlink(tmp_name)
                print(f"Restored {name}: {len(data)} bytes")


if __name__ == "__main__":
    restore()
