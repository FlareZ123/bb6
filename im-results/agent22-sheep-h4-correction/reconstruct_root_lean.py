"""Restore the locally checked H4 chain and blank-orbit exclusion."""
from pathlib import Path
import base64, hashlib, io, tarfile
root = Path(__file__).parent
raw = base64.b64decode((root / "h4-root-lean.tar.xz.b64").read_text())
assert hashlib.sha256(raw).hexdigest() == "a7c474addb8b4341a41b91f5549a4f8e48c83c13fc01615246b050940c2b7e42"
hashes = {
    "H4YParent.lean": "ef26ded894f814ab96df6525fa1c58b50ee8385f277e4943fd18df7862b50d87",
    "H4XCore.lean": "c3ea1e75884480b72062cc4c19ccc33f053349eb812cbe22c209daf68a48a794",
    "H4XRows.lean": "ba5ce16bbf4ac25f41c15169b4b4c0c088694f5f84e6d1c07dc9ca928b182e57",
    "H4BlankReach.lean": "0aae64a2acf93d91058f260bc6f6a388a084a4ad9a471ff90caac21a2bf61b0d",
}
with tarfile.open(fileobj=io.BytesIO(raw), mode="r:xz") as tar:
    assert set(tar.getnames()) == set(hashes)
    for name, digest in hashes.items():
        data = tar.extractfile(name).read()
        assert hashlib.sha256(data).hexdigest() == digest
        (root / name).write_bytes(data)
        print(name)
