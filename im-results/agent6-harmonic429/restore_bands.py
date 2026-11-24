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
    "highcomplete.tar.xz.b64": (
        "105d246cd4a69a78c5152f805511017a22c49f482dd505796a64ebe66a3db7a5",
        {
            "BB429HighTrue.lean": "8d570043b334b9ccadeb04267bd1392ad26a452b53ba392e24d317fcbc551d43",
            "BB429ElevenDivisor.lean": "6fbaeeb96e2e155dd37b6b096fb443af0b2249087ab9129ccaedfb42d66f97ed",
            "BB429ZeroTrueDivisor.lean": "57c55986b5dde6c45a2251be8dd03b5b80a99bf96fc2c9de739e8ac3fa189d5e",
            "BB429ElevenHigh.lean": "ea2db7517e845233d33b655c3012949577e87be28845d43d2b98c8dd4438d5e0",
            "BB429ZeroHigh.lean": "7260171f7ac35d3003a11c1224889ae4c41bad39611593fe1099fc00af752546",
            "BB429HighComplete.lean": "ff530f50b2dc669433e5166f4a270f3e8eca7fc3418bc7718d3b9cb42bde6f9f",
            "BB429LowCounterexample.lean": "394596eb3979555dafc92188e05a1a8bbc60db922ab47db9a318b93ccadcab3d",
        },
    ),
    "fastwide.tar.xz.b64": (
        "a8323620bc816885193c1ef072134e8ad2f4dac31a1d6f7182d86433f731e293",
        {
            "BB429FastReplay.lean": "6b020e000be82545e2c5978756d617a06ce9c13c36f3d642d14bdc8963a3b852",
            "BB429FastBinary.lean": "e0319cff5431a98198d8b236d8c280bfc1f3808d2972e1c1e9e2d5f9a1b0469a",
            "rank_return_wide.cpp": "d8502edf6dc4726af7016dd454c95f4a35187d42882fb4ad758e831a42dec518",
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
