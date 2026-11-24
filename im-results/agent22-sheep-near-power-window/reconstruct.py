from pathlib import Path
import base64
import hashlib
import lzma

here = Path(__file__).resolve().parent
raw = lzma.decompress(base64.b64decode((here / "NearPowerWindow.lean.xz.b64").read_bytes(), validate=True))
assert hashlib.sha256(raw).hexdigest() == "13438b2416415dfb9533ff99301b7e9852bf78d2fdf843c6a9981fe6b1b7fe1e"
target = here / "NearPowerWindow.lean"
target.write_bytes(raw)
print(target)
