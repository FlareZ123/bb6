import base64, gzip, hashlib, os, tempfile
from pathlib import Path
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
PARTS = [f"rank-gzip-{i:02d}.txt" for i in range(1, 5)]
HASH = "11d55ef352336c78e24ca0ca57effa68d02393dc70254806f7515596b7ada8b5"
encoded = "".join((ROOT / p).read_text() for p in PARTS)
source = gzip.decompress(base64.b64decode(encoded, validate=True))
assert hashlib.sha256(source).hexdigest() == HASH
dest = ROOT / "RankS.lean"
with FileLock(str(dest) + ".lock"):
    with tempfile.NamedTemporaryFile(dir=ROOT, delete=False) as tmp:
        tmp.write(source)
        tmpname = tmp.name
    os.replace(tmpname, dest)
print("Restored", dest)
