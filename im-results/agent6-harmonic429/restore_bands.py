"""Restore the locally checked Lean modules in bandproof.tar.xz.b64."""
from pathlib import Path
import base64
import hashlib
import io
import tarfile

root = Path(__file__).resolve().parent
raw = base64.b64decode((root / "bandproof.tar.xz.b64").read_text())
assert hashlib.sha256(raw).hexdigest() == "569bc957d1a774ed6afff5bfc6dc3bb54a8b72bdf5964c65ac6235057a4d4454"
expected = {
    "BB429SectionBands.lean": "18b6667c73db590db421015b23a19c0c1887bbcb0688e289bc60114940b711cd",
    "BB429BandBridge.lean": "e9f0e908cbac40ba0feb0a7c873d1b2f56b81525502abd6b6b4ceb8667abc974",
    "BB429BandTransfer.lean": "e6503f75b637418f17513427f89425c62a73cb755b291f04f1d011cbb2fb931b",
}
with tarfile.open(fileobj=io.BytesIO(raw), mode="r:xz") as archive:
    assert set(archive.getnames()) == set(expected)
    for name, digest in expected.items():
        src = archive.extractfile(name).read()
        assert hashlib.sha256(src).hexdigest() == digest
        (root / name).write_bytes(src)
        print(name, digest)
