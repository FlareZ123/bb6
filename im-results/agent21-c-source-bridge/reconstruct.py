"""Restore and hash-verify Agent 21's exact Lean predecessor sources.

Compressed solely to make concurrent GitHub API commits small.
Requires Python filelock. Every write is atomic under a common lock.
"""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "CBack.lean": "84767aed6924f78e7aae1bc483a92f5aa068ccbb8f12fcfd888fa13777819474",
    "CMod32.lean": "52f852d6468489fe6bf5f1fb8963a8ed8ab49d6ea43a811862bf8787c1e9f086",
    "CMod128Six.lean": "6a2ea646e079638cd0f4c2dffc3abc0930da8a5ee9af97ffda11489f1dea80e3",
    "CMod32TwentyTwo.lean": "ea45ae11e45ae511f224068cd1d38c8392a47f1a981c0ba4282132b8ef552c95",
    "CHubSplit.lean": "3b637e13341f07f16213dc5e41cea05a6453252d209cfa2ba33bc51f5bd99940",
    "CMod128Eighteen.lean": "5b8e37c9c95151c63068b8df722e2cf5dfdd4803d61c49329e80db3e7c6a48e7",
    "CMod128SeventyTwo.lean": "41096495f6689337a522a17134e6635c549ad43f143d300ac1a696fb3a404cc4",
}

with FileLock(str(ROOT / ".agent21-lean-sources.lock")):
    for name, digest in SOURCES.items():
        encoded = "".join((ROOT / (name + ".xz.b64")).read_text(encoding="ascii").split())
        data = lzma.decompress(base64.b64decode(encoded, validate=True))
        actual = hashlib.sha256(data).hexdigest()
        if actual != digest:
            raise ValueError(f"{name}: SHA-256 mismatch: {actual}")
        with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
            tmp.write(data)
            tmp.flush()
            os.fsync(tmp.fileno())
            tmpname = tmp.name
        os.replace(tmpname, ROOT / name)
        print(f"Restored {name}: {len(data)} bytes, SHA-256 {digest}")
