import base64
import hashlib
import io
import lzma
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HASHES = {
    "SheepBand.lean": "6cc9fcee30e1d8e284577025ad9951136051596056bd67e522ceeaa1751cb9a9",
    "SheepBandCounting.lean": "10db78c7b8479485b81be2f2d26f0d82f32136ef8a98a18008304b2a0317d231",
    "SheepBandSource.lean": "b46ada78c84dd8485f4c83645c67a9122aa849e78848eb4455d06787d5c0605a",
}
with tarfile.open(fileobj=io.BytesIO(lzma.decompress(base64.b64decode((ROOT / "proofs.tar.xz.b64").read_text()))), mode="r:") as archive:
    assert set(archive.getnames()) == set(HASHES)
    for name, digest in HASHES.items():
        data = archive.extractfile(name).read()
        assert hashlib.sha256(data).hexdigest() == digest, name
        (ROOT / name).write_bytes(data)
        print(name)
