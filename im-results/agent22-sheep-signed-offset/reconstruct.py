from pathlib import Path
import base64
import hashlib
import lzma

base = Path(__file__).resolve().parent
data = lzma.decompress(base64.b64decode((base / "SignedOffset.lean.xz.b64").read_bytes(), validate=True))
assert hashlib.sha256(data).hexdigest() == "2779375365f7b373d85aea4cb9c14eb4bada2ca7205ddcadae778cf3f7a38966"
(base / "SignedOffset.lean").write_bytes(data)
print("Reconstructed SignedOffset.lean")
