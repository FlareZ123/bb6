import base64,hashlib,io,tarfile
from pathlib import Path
p=Path(__file__).parent
b=base64.b64decode((p/'returnfamily.tar.xz.b64').read_text())
assert hashlib.sha256(b).hexdigest()=='141773ca23eed7344c3011daaac7f57a27b9386d5a4ee25361a6a5b88475dcd5'
names={'lean/Raw59Variant.lean','lean/ReturnRegular.lean','lean/ReturnFamily.lean',*[f'lean/ReturnCert{i}.lean' for i in range(4)]}
with tarfile.open(fileobj=io.BytesIO(b),mode='r:xz') as t:
    assert set(t.getnames())==names
    for m in t.getmembers():
        assert m.isfile()
        path=p/m.name
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(t.extractfile(m).read())
