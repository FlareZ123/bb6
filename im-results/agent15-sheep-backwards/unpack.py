from pathlib import Path
from filelock import FileLock
import base64,hashlib,lzma
root=Path(__file__).resolve().parent
dst=root/"SheepResidue.lean"
raw=lzma.decompress(base64.b64decode((root/"SheepResidue.lean.xz.b64").read_text()))
assert hashlib.sha256(raw).hexdigest()=="a06ac3584faf3f0f6bdc00c1b9609c140fc5e89a98e11b21312408676a71d2fe"
with FileLock(str(dst)+".lock"):
    tmp=dst.with_suffix(".tmp")
    tmp.write_bytes(raw)
    tmp.replace(dst)
print("Verified and restored",dst)
