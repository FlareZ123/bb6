"""Restore the locally checked Lean modules from the proof archives."""
from pathlib import Path
import base64
import hashlib
import io
import tarfile

root = Path(__file__).resolve().parent
archives = {
    "bandproof.tar.xz.b64": (
        "569bc957d1a774ed6afff5bfc6dc3bb54a8b72bdf5964c65ac6235057a4d4454",
        {
            "BB429SectionBands.lean": "18b6667c73db590db421015b23a19c0c1887bbcb0688e289bc60114940b711cd",
            "BB429BandBridge.lean": "e9f0e908cbac40ba0feb0a7c873d1b2f56b81525502abd6b6b4ceb8667abc974",
            "BB429BandTransfer.lean": "e6503f75b637418f17513427f89425c62a73cb755b291f04f1d011cbb2fb931b",
        },
    ),
    "highbandproof.tar.xz.b64": (
        "42155abb0dbd53c3f5d28c4657727977a2424d487a7ca6fac447fc5a35c4021d",
        {
            "BB429HighBand.lean": "0ce3191babea5c7686366c0ef5f109caa8a02f0f911d9485e72b93dc0c2bc0c8",
            "BB429BoundaryDivisor.lean": "35d4adc93f1b7f774a37e9ffad011321069e4303ecb951c5c0f6d50896099a2b",
            "BB429HighTransfer.lean": "812c9af88041a8e16a9b08b986e6607a5e1ca41748ea5f934ca813ddba74ebbe",
        },
    ),
}
for filename, (archive_digest, expected) in archives.items():
    raw = base64.b64decode((root / filename).read_text())
    assert hashlib.sha256(raw).hexdigest() == archive_digest
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r:xz") as archive:
        assert set(archive.getnames()) == set(expected)
        for name, digest in expected.items():
            src = archive.extractfile(name).read()
            assert hashlib.sha256(src).hexdigest() == digest
            (root / name).write_bytes(src)
            print(name, digest)
