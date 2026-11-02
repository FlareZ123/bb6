"""Reconstruct checked Machine C bounce exact-image Lean modules.

Requires only Python standard library. Files are replaced atomically.
"""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "BounceExact.lean": (
        "e599ff54129270cb81e50d12fa3773dec9039feb9fe8c15b54def37bf9339538",
        "b4ccfd460aa2f43f89f2f72976f0149d86e1255867197e380dfd220179d2eafd",
    ),
    "BounceOriginal.lean": (
        "30206b9d1c90f951ffd5091addb3ff8236cb830164b7972ea86c45e5a679e4ae",
        "8bf6dcbe53d5b4a36fae385f63042410fc5218ab047652c5f4efdb1d58ac42f0",
    ),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


for filename, (expected_source, expected_archive) in SOURCES.items():
    packed = base64.b64decode((ROOT / (filename + ".xz.b64")).read_bytes(), validate=False)
    assert sha256(packed) == expected_archive, filename + ": archive hash mismatch"
    source = lzma.decompress(packed)
    assert sha256(source) == expected_source, filename + ": source hash mismatch"

    with tempfile.NamedTemporaryFile(dir=ROOT, prefix="." + filename, delete=False) as tmp:
        temporary = Path(tmp.name)
        tmp.write(source)
        tmp.flush()
        os.fsync(tmp.fileno())
    os.replace(temporary, ROOT / filename)
    print(f"{filename}: verified SHA256 {expected_source}, {len(source)} bytes")
