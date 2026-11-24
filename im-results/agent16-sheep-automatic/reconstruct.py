from pathlib import Path
import base64, hashlib, lzma
p = Path(__file__).parent
b = base64.b64decode((p / "SheepAutomata.lean.xz.b64").read_text())
assert hashlib.sha256(b).hexdigest() == "b178d01fc004d64cc735e77811a969903631cc719b772643df8a97a7bb34e9aa"
s = lzma.decompress(b)
assert hashlib.sha256(s).hexdigest() == "9abe5c90439901736b47737087eb8f95c7efde1ce4ec7f789f7cc21d3cc1604b"
(p / "SheepAutomata.lean").write_bytes(s)
