from pathlib import Path
import base64, lzma, hashlib
p = Path(__file__).parent
b = base64.b64decode((p / "SheepCounted.lean.xz.b64").read_text())
assert hashlib.sha256(b).hexdigest() == "4314301311be3a96ffa5efbdd88f45dc16248bcaac53707bf7d2d8f4296f793b"
s = lzma.decompress(b)
assert hashlib.sha256(s).hexdigest() == "2255c67d617f502f9fd37b4b8617ffe6aa9effccda7ffdf50017bd2f517da09d"
(p / "SheepCounted.lean").write_bytes(s)

import io, tarfile
archive = base64.b64decode((p / "extensions.tar.xz.b64").read_text())
assert hashlib.sha256(archive).hexdigest() == "0931924badb810fafd66cf28220861da1f94949d9cf23064feaaf8a99562b002"
hashes = {
    "SheepStream.lean": "e66257de8c15b55c93740caf71978edafe4812a099df7687330e51d852a73e0b",
    "SheepPotential.lean": "960d6f5c2bddbc26aa516a17a69fcdfbd44148f25a825e2bdfc5ffb75d244afb",
    "SheepCountedBridge.lean": "022357c261b3045aa78f75622539de3fe89643aae6b32160f329523752e6fd9c",
}
with tarfile.open(fileobj=io.BytesIO(lzma.decompress(archive)), mode="r:") as a:
    assert set(a.getnames()) == set(hashes)
    for name, digest in hashes.items():
        data = a.extractfile(name).read()
        assert hashlib.sha256(data).hexdigest() == digest
        (p / name).write_bytes(data)
