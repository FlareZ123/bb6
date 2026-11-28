from pathlib import Path
import base64
import hashlib
import lzma

ROOT = Path(__file__).resolve().parent
FILES = {
    "Box33D17V12IClosed.lean": "2e239cc3fc5d44efd91be1c886656077680aac7993980849a13e9353261a8e4d",
    "Box33D17V12IInvariant.lean": "60251a8c230a89a2d26a41105372ad1e7f48a435816a5cde3289e6d1d7c34374",
}
for name, expected in FILES.items():
    data = lzma.decompress(base64.b64decode((ROOT / (name + ".xz.b64")).read_text()))
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"SHA256 mismatch for {name}")
    (ROOT / name).write_bytes(data)
    print(name, expected)
