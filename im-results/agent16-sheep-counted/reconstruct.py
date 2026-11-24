from pathlib import Path
import base64, lzma, hashlib
p = Path(__file__).parent
b = base64.b64decode((p / "SheepCounted.lean.xz.b64").read_text())
assert hashlib.sha256(b).hexdigest() == "4314301311be3a96ffa5efbdd88f45dc16248bcaac53707bf7d2d8f4296f793b"
s = lzma.decompress(b)
assert hashlib.sha256(s).hexdigest() == "2255c67d617f502f9fd37b4b8617ffe6aa9effccda7ffdf50017bd2f517da09d"
(p / "SheepCounted.lean").write_bytes(s)
