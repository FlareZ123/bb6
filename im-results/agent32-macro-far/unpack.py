"""Materialize the digest-checked local Lean and discovery source snapshot."""
import base64,hashlib,io,tarfile
from pathlib import Path
root=Path(__file__).resolve().parent
raw=base64.b64decode((root/'source.tar.xz.b64').read_text(),validate=True)
assert hashlib.sha256(raw).hexdigest()=='f2f9ab5e713db4738fb47c2eeeaefef0cb02f42f8316b679052e9773533680d1'
with tarfile.open(fileobj=io.BytesIO(raw),mode='r:xz') as a:
    for m in a.getmembers():
        p=(root/m.name).resolve()
        assert p.is_relative_to(root) and m.isfile()
        p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(a.extractfile(m).read())
