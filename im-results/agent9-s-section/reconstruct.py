import base64, gzip, hashlib, os, tempfile
from pathlib import Path
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
PARTS = ["lean-gzip-01.txt", "lean-gzip-02.txt", "lean-gzip-03.txt",
         "lean-gzip-04a.txt", "lean-gzip-04b.txt"]
HASH = "0796a6dc7a3c1ff4beecd888a0545bf8ee2557497d9e0bec8da5e25a5d2b816c"
encoded = "".join((ROOT / p).read_text() for p in PARTS)
source = gzip.decompress(base64.b64decode(encoded, validate=True))
assert hashlib.sha256(source).hexdigest() == HASH
dest = ROOT / "SBurst.lean"
with FileLock(str(dest) + ".lock"):
    with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
        tmp.write(source)
        tmpname = tmp.name
    os.replace(tmpname, dest)
print("Restored", dest)
