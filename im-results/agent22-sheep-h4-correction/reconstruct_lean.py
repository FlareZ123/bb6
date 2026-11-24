"""Restore the locally kernel-checked H4 proof modules."""
from pathlib import Path
import base64, hashlib, io, tarfile
root = Path(__file__).parent
raw = base64.b64decode((root / "h4-lean.tar.xz.b64").read_text())
assert hashlib.sha256(raw).hexdigest() == "1c8a38de3ef963a98b237a4e441566b5454b9ae6f9d516810c6d70eb72b197c9"
hashes = {
    "H4AllHiddenCore.lean": "e4606641157d4ab6b088fc81c91b9e5a28e8ceb935a49b7519774a4faa15ed7a",
    "H4LowRows.lean": "f167906bb35abe9fa74234982021c94d3e96bca2b3282f1896262272fd124c9c",
    "H4HighRoot.lean": "6f0630c1ead2512fec754d92bff77baa972c798af628e1abb51a0db7b77c8d66",
    "H4Sufficiency.lean": "c5b1111592c3c45c49a8952d3ece1825604be5e8eba024922621cac7c2673e50",
}
with tarfile.open(fileobj=io.BytesIO(raw), mode="r:xz") as tar:
    assert set(tar.getnames()) == set(hashes)
    for name, digest in hashes.items():
        data = tar.extractfile(name).read()
        assert hashlib.sha256(data).hexdigest() == digest
        (root / name).write_bytes(data)
        print(name)
