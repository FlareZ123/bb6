import base64, hashlib, io, tarfile
from pathlib import Path

root = Path(__file__).resolve().parent
data = base64.b64decode((root / "return1582.tar.xz.b64").read_text().strip(), validate=True)
assert hashlib.sha256(data).hexdigest() == "3f6507609a67c526ab75c1ec34fe26112f48d5970abc46f8cc4861766f966ee0"
with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as archive:
    for member in archive:
        assert member.name in ("lean/Raw59ReturnMath.lean", "lean/Raw59ReturnMachine.lean") and member.isfile()
        (root / member.name).write_bytes(archive.extractfile(member).read())
