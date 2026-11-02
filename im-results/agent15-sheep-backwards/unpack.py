from pathlib import Path
from filelock import FileLock
import base64,hashlib,lzma
root=Path(__file__).resolve().parent
dst=root/"SheepResidue.lean"
raw=lzma.decompress(base64.b64decode((root/"SheepResidue.lean.xz.b64").read_text()))
assert hashlib.sha256(raw).hexdigest()=="47a67598828c3a21f0075cccc3665dc0bc6510793d3ea4527e4d06a8143e96af"
with FileLock(str(dst)+".lock"):
    tmp=dst.with_suffix(".tmp")
    tmp.write_bytes(raw)
    tmp.replace(dst)
print("Verified and restored", dst)
