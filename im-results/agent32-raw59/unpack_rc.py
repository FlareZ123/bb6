from pathlib import Path
import base64, hashlib, lzma
root=Path(__file__).resolve().parent
data=lzma.decompress(base64.b64decode((root/'Raw59RCShared.lean.xz.b64').read_text()))
assert hashlib.sha256(data).hexdigest()=='207cc91f598334ec6a927a43f8b6c087b6e87d87b8a5a6567842d73c713fe686'
(root/'Raw59RCShared.lean').write_bytes(data)
