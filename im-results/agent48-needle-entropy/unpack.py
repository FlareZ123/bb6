from pathlib import Path
import base64, hashlib, lzma
root = Path(__file__).resolve().parent
for name, expected in [["NeedleSubpower.lean","685d82e054aa8676f71234a11a2a32ef03474101"],["NeedleEntropyWords.lean","bd57106eb5fb6be76bf0ec99ac81496d862fee34"],["NeedleEntropyBound.lean","2e51a286f8b0d1046a583011f422507b8b032bba"]]:
    b = lzma.decompress(base64.b64decode((root / (name + ".xz.b64")).read_bytes()))
    actual = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
    assert actual == expected, (name, actual, expected)
    (root / name).write_bytes(b)
    print(name, actual)
