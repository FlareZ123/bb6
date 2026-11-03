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
    "inverse_section.py": (
        "a07d53884dd32df4144d6a2d637f5878b4fa2e0776b12141b902195e848c4c0a",
        "0f3fa0447f54b6bbb01b49324607a3683bbc812647e591cf15059940bc3c5bdd",
    ),
    "SectionFull.lean": (
        "c647c909662408ec6a2a32515d918897f187116a02ddaddfbee9a84f4f03b414",
        "24ec98c4bd7420280451f88c99b0d90982179212e9a7a2e793d5e506e29f3eda",
    ),
    "SectionFullOriginal.lean": (
        "349b1778028c024e4b1bb8d9f913c9d5944285cadf02f20cec71cbfb7f802056",
        "0e16ebfc402370c1b78c4ca77a011c038af53ec216d9e5d1b9fae1e3124d8ad9",
    ),
    "Fan.lean": (
        "cbc48711f1f2c42ce1f975ac8c2a062a9604e025b1b937361e13d0ca33654184",
        "587c636e2c00c74c54ed564f74b4dd7a39bae9dad143f4af77bffb403b95a9af",
    ),
    "FanOriginal.lean": (
        "23ca70b389b285102874f92f89e0e7210a0b672771411c2586b38414789f37d5",
        "2df84f85bb28e306f978d35303465816cc257c087d2c8d6aa8a1ac54b7f07058",
    ),
    "FanExact.lean": (
        "0a1bf21ea809febe18ca0c2d90f70f59ba4f4c37968215e87b0bd10ae779a1ad",
        "95c74a15b305fc6db7a19b96b5e74fad922c7577b8c1e22a7fb65fb7d2ef27d5",
    ),
    "FanExactOriginal.lean": (
        "1ffd89dce7fe6773633a0353ee10c98404e8053f5677431396f44ff149c3dfa4",
        "bc6acbc96ad56b85a423b98c435f6ac8679e925235aec838fe9c13b251d4dfb9",
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
