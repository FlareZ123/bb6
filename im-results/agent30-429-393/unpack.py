"""Restore both exact #429 Lean certificates under a local exclusive file lock."""
import base64
import fcntl
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "BB429No393mod512.lean": "205eb810e98022eb2641dcd8ebce07fedc564064dc00dfec01faca0c68fa280e",
    "BB429No265mod512.lean": "ea2cac2c571fcc26f25f32bf37d025ae55dd85f404afb4395913422c1d9bbe3a",
    "BB429No137mod1024.lean": "e5b007e4372467d9f7d9f2d72e064b70bf551ee4b7bc23d9fae796fc9cdbd3d8",
    "BB429No521mod1024.lean": "d306d4e562d64e96777cd13b32c1ae767783b09f0783d667bb9283657f8e2e59",
}

with (ROOT / ".unpack.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    for name, expected in SOURCES.items():
        raw = lzma.decompress(base64.b64decode((ROOT / (name + ".xz.b64")).read_text().strip()))
        digest = hashlib.sha256(raw).hexdigest()
        if digest != expected:
            raise ValueError(f"Lean source SHA256 mismatch for {name}: {digest}")
        fd, temporary = tempfile.mkstemp(prefix=".lean429-", dir=ROOT)
        try:
            with os.fdopen(fd, "wb") as handle:
                handle.write(raw)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, ROOT / name)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)
        print(f"Verified {name}: {len(raw)} bytes, sha256={digest}")
