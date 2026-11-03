"""Restore Agent 2 full E-row Lean proof with checksum and atomic replacement."""
import base64
import hashlib
import lzma
import os
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
EXPECTED = "ac5570b5bb543de79041c48b2784687485a21a64cb1845662022ff68bb07012c"

with FileLock(str(ROOT / ".e-regular.lock")):
    packed = base64.b64decode((ROOT / "ERemaining.lean.xz.b64").read_text().strip(), validate=True)
    if hashlib.sha256(packed).hexdigest() != EXPECTED:
        raise ValueError("Checksum mismatch in complete E-row source proof")
    source = lzma.decompress(packed)
    with NamedTemporaryFile(dir=ROOT, prefix=".e-source-", delete=False) as tmp:
        tmp.write(source)
        tmp.flush()
        os.fsync(tmp.fileno())
        staged = Path(tmp.name)
    os.replace(staged, ROOT / "ERemaining.lean")
print("Verified and restored ERemaining.lean")
