from pathlib import Path
import base64
import hashlib
import lzma

folder = Path(__file__).resolve().parent
data = lzma.decompress(base64.b64decode((folder / "SheepAffineSpecial.lean.xz.b64").read_bytes()))
assert hashlib.sha256(data).hexdigest() == "eeb22e6b0263e9fca79d1b8263a30a2d7f63b66820ee9be39f6f0f4243418c4f"
(folder / "SheepAffineSpecial.lean").write_bytes(data)
