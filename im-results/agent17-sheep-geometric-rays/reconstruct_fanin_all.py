"""Restore three independently checked Sheep power-fan-in Lean sources."""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

from filelock import FileLock

ROOT = Path(__file__).resolve().parent
CHECKSUMS = {
    "A3PowerFanin.lean": "2b2ba78c1460372e73c41d78a92d6b760a1188e931f501067a7207df6064473d",
    "A7PowerFanin.lean": "ecab82cb5281dab925053a135f575a3b1b8c46a19c1493a45488038a00d379e9",
    "A15PowerFanin.lean": "153f88695cc8ed488271c943f3d06de911d4fe67716d7b346a693383cb301586",
}
with FileLock(str(ROOT / ".fan-in-lean.lock")):
    for name, expected in CHECKSUMS.items():
        blob = (ROOT / (name + ".xz.b64")).read_text(encoding="ascii")
        source = lzma.decompress(base64.b64decode(blob))
        actual = hashlib.sha256(source).hexdigest()
        if actual != expected:
            raise ValueError(f"Checksum mismatch in {name}: {actual}")
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix=".fan-in-", suffix=".lean", delete=False) as stream:
            temp = Path(stream.name)
            stream.write(source)
        os.replace(temp, ROOT / name)
        print(f"Verified {name}: {len(source)} bytes, SHA256 {actual}")
